r"""
검사건 리스트 자동 갱신 스크립트
==================================
recv_xml의 023(수입신고처리결과통보서)에서 C/S검사 결과가 "Y"인 신고번호를
검사대상으로 판정하고, 5EM(검사계획통보)이 있으면 상세(검사항목·담당자)로 보완하며,
send_xml의 929(수입신고서)로 통관계획·대행사·포장갯수·수입화주·H B/L·장치장소를 채우고,
유니패스 화물통관진행정보조회 API로 B/L번호를 조회해 창고 반입일까지 채운 뒤
TONDA-CONVERT 레포의 inspection/data.json에 게시합니다.

★ 표준 라이브러리만 사용합니다 (xml.etree, urllib) — pip install 불필요.
★ 매 실행마다 GitHub에 이미 게시된 기존 행을 먼저 받아온 뒤, 이번에 스캔된
  신고번호만 추가/갱신합니다 — 스캔 범위(기본 최근 3일) 밖의 과거 데이터는
  삭제되지 않고 그대로 유지됩니다.

실행 전 준비:
  1) config.ini 에 [github] 섹션 추가:
       [github]
       token = ghp_xxx...   (repo 권한 있는 GitHub Personal Access Token)
     발급: https://github.com/settings/tokens/new?scopes=repo
  2) config.ini 에 [unipass] 섹션 추가 (반입일 자동조회용, 없으면 반입일만 비워둔 채 동작):
       [unipass]
       cargo_key = ...      (유니패스 OPEN API "화물통관진행정보조회"(API001) 인증키)
  3) config.ini 의 [paths] recv_dir / send_dir 가 실제 경로를 가리키는지 확인

실행: python inspection_autoupdate.py
스케줄: Windows 작업 스케줄러에 "30분마다 반복" 트리거로 등록 권장
        (schtasks /create /tn "검사건리스트 자동갱신" /tr "python C:\...\inspection_autoupdate.py"
                  /sc minute /mo 30 /ru SYSTEM)
"""
import base64
import configparser
import glob
import json
import os
import re
import sys
import time
import urllib.error
import urllib.parse
import urllib.request
import xml.etree.ElementTree as ET
from datetime import datetime, timedelta

BASE_DIR = os.path.dirname(os.path.abspath(__file__))
_config = configparser.ConfigParser()
_config.read(os.path.join(BASE_DIR, 'config.ini'), encoding='utf-8')

RECV_DIR = _config.get('paths', 'recv_dir', fallback='')
SEND_DIR = _config.get('paths', 'send_dir', fallback='')
GH_TOKEN = _config.get('github', 'token', fallback='').strip()
UNIPASS_KEY = _config.get('unipass', 'cargo_key', fallback='').strip()

# 유니패스 화물통관진행정보조회 (서비스ID API001) — 반입일 자동 채움에 사용
CARGO_API = 'https://unipass.customs.go.kr:38010/ext/rest/cargCsclPrgsInfoQry/retrieveCargCsclPrgsInfo'
# 신고일이 이보다 오래된 행은 반입일 재조회를 포기한다 (끝내 안 채워지는 행을 30분마다 계속
# 두드리면 게시 건수가 쌓일수록 매 실행의 API 호출이 무한정 늘어나므로)
ARRIVAL_LOOKUP_DAYS = 30

REPO_OWNER = 'a90894048-creator'
REPO_NAME = 'TONDA-CONVERT'
FILE_PATH = 'inspection/data.json'
API_URL = f'https://api.github.com/repos/{REPO_OWNER}/{REPO_NAME}/contents/{FILE_PATH}'
RAW_URL = f'https://raw.githubusercontent.com/{REPO_OWNER}/{REPO_NAME}/main/{FILE_PATH}'

# 929에 찍히는 대행사 표기가 채널별로 다름 — 정확히 일치하는 것만 통다 계열로 인정
CHANNEL_MAP = {
    '통다글로벌로지스틱': '쿠팡',
    '통다그로벌로지스틱': '교동',
    '주식회사 통다글로벌로지스틱스': '통다',
}

DAYS_BACK = 3  # 오늘 포함 최근 N일의 recv_xml/send_xml을 스캔 (023→5EM 지연을 감안한 범위)


# ── XML 파싱 유틸 (watcher.py / relay_server.py 와 동일한 네임스페이스 제거 방식) ──
def strip_ns(xml_text: str) -> str:
    clean = re.sub(r'\s+xmlns(?::[a-zA-Z0-9_]+)?="[^"]*"', '', xml_text)
    clean = re.sub(r'\s+xsi:schemaLocation="[^"]*"', '', clean)
    clean = re.sub(r'<(/?)[a-zA-Z0-9_]+:([a-zA-Z0-9_])', r'<\1\2', clean)
    return clean


def read_file(path: str) -> str:
    for enc in ('utf-8', 'cp949', 'euc-kr'):
        try:
            with open(path, 'r', encoding=enc) as f:
                return f.read()
        except UnicodeDecodeError:
            continue
        except Exception:
            return ''
    return ''


def parse_xml(path: str):
    content = read_file(path)
    if not content:
        return None
    try:
        return ET.fromstring(strip_ns(content))
    except ET.ParseError:
        return None


def txt(root, path: str, default: str = '') -> str:
    if root is None:
        return default
    node = root.find(path)
    return (node.text or '').strip() if node is not None else default


def iso_date(raw: str) -> str:
    return f'{raw[0:4]}-{raw[4:6]}-{raw[6:8]}' if len(raw) >= 8 else ''


def short_date(raw: str) -> str:
    return f'{int(raw[4:6])}/{int(raw[6:8])}' if len(raw) >= 8 else ''


def recent_dates(n_back: int):
    today = datetime.now()
    return [(today - timedelta(days=i)).strftime('%Y%m%d') for i in range(n_back + 1)]


# ── 문서 타입별 파싱 ──────────────────────────────────────────
def parse_5em(root) -> dict:
    decl = root.find('Declaration')
    decl_no = txt(root, 'ID') or txt(root, 'Declaration/ID')
    content = txt(root, 'AdditionalInformation/Content')
    entries = []
    consign = decl.find('Consignment') if decl is not None else None
    if consign is not None:
        for item in consign.findall('ConsignmentItem'):
            seq = txt(item, 'SequenceNumeric').lstrip('0')
            desc = txt(item, 'Commodity/CargoDescription')
            if desc:
                entries.append((int(seq or 0), f'{seq}란 {desc}'))
    entries.sort(key=lambda e: e[0])
    summary = ',\n'.join(e[1] for e in entries)
    remark = f'{summary} — {content}' if (summary and content) else (summary or content or 'LCL 검사건')
    return {
        'declNo': decl_no,
        'hbl': txt(root, 'Declaration/AdditionalDocument/ID'),
        'officer': txt(root, 'Authenticator/Name') or '미상',
        'warehouse': txt(root, 'Declaration/Consignment/Warehouse/ID'),
        'remark': remark,
    }


def parse_929(root) -> dict:
    issue = txt(root, 'IssueDateTime')
    items = {}
    # GovernmentAgencyGoodsItem은 root의 직속 자식이 아니라 GoodsShipment 아래에 있음 —
    # './/'로 깊이 상관없이 전부 찾는다
    for item in root.findall('.//GovernmentAgencyGoodsItem'):
        seq = txt(item, 'SequenceNumeric').lstrip('0')
        desc = txt(item, 'Commodity/CargoDescription')
        if seq:
            items[seq] = desc
    hbl = ''
    for tcd in root.findall('.//TransportContractDocument'):
        if txt(tcd, 'TypeCode') == '714':
            hbl = txt(tcd, 'ID')
            break
    return {
        'declNo': txt(root, 'ID'),
        'date': iso_date(issue),
        'reportDate': short_date(issue),
        'plan': txt(root, 'GovernmentProcedure/CurrentCode'),
        'agency': txt(root, 'GoodsShipment/Agent/Name'),
        'packages': txt(root, 'TotalPackageQuantity'),
        'importer': txt(root, 'Importer/Name'),
        'warehouse': txt(root, 'GoodsShipment/Warehouse/ID'),
        'hbl': hbl,
        'items': items,
    }


def parse_023(root) -> dict:
    decl = root.find('Declaration')
    decl_no = txt(root, 'Declaration/FunctionalReferenceID') or txt(root, 'Declaration/ID')
    accept = txt(root, 'Declaration/AcceptanceDateTime')
    issue = txt(root, 'IssueDateTime')
    flagged = []
    if decl is not None:
        for gs in decl.findall('GoodsShipment'):
            if txt(gs, 'AdditionalInformation/StatementCode') in ('Y', 'F'):
                flagged.append(txt(gs, 'SequenceNumeric').lstrip('0'))
    flagged.sort(key=lambda s: int(s or 0))
    return {
        'declNo': decl_no,
        'issueRaw': issue,
        'date': iso_date(accept),
        'reportDate': short_date(accept),
        'officer': txt(root, 'Authenticator/Name'),
        'flaggedSeqs': flagged,
    }


# ── 스캔 + 병합 ───────────────────────────────────────────────
def scan():
    rows5em, rows929, rows023 = {}, {}, {}
    dates = recent_dates(DAYS_BACK)

    for d in dates:
        for path in glob.glob(os.path.join(RECV_DIR, 'complete', d, '*.xml')):
            content = read_file(path)
            if not content:
                continue
            if 'GOVCBR5EM' in content:
                root = parse_xml(path)
                r = parse_5em(root) if root is not None else None
                if r and r['declNo'] and r['declNo'] not in rows5em:
                    rows5em[r['declNo']] = r
            elif 'GOVCBR023' in content:
                root = parse_xml(path)
                r = parse_023(root) if root is not None else None
                if r and r['declNo']:
                    prior = rows023.get(r['declNo'])
                    if not prior or r['issueRaw'] < prior['issueRaw']:
                        rows023[r['declNo']] = r

        for path in glob.glob(os.path.join(SEND_DIR, 'complete', d, 'GOVCBR929*.xml')):
            root = parse_xml(path)
            if root is None:
                continue
            r = parse_929(root)
            if r['declNo']:
                rows929[r['declNo']] = r

    return rows5em, rows929, rows023


def build_rows(rows5em, rows929, rows023) -> dict:
    result = {}
    for decl_no, r023 in rows023.items():
        if not r023['flaggedSeqs']:
            continue
        r5em = rows5em.get(decl_no)
        r929 = rows929.get(decl_no)
        has_detail = r5em is not None

        if has_detail:
            remark = r5em['remark']
        else:
            parts = []
            for seq in r023['flaggedSeqs']:
                desc = (r929['items'].get(seq) if r929 else '') or ''
                parts.append(f'{seq}란' + (f' {desc}' if desc else ''))
            remark = (',\n'.join(parts) + '\n— ' if parts else '') + '검사계획통보 대기중'

        row = {
            'declNo': decl_no,
            'declKnown': True,
            'date': r023['date'],
            'reportDate': r023['reportDate'],
            'officer': (r5em['officer'] if r5em else '') or r023['officer'] or '미상',
            'hbl': (r5em['hbl'] if r5em else '') or (r929['hbl'] if r929 else ''),
            'warehouse': (r5em['warehouse'] if r5em else '') or (r929['warehouse'] if r929 else ''),
            'remark': remark,
            'plan': '', 'agency': '', 'channel': '', 'packages': '', 'importer': '', 'arrival': '',
            'verified': has_detail,
        }
        if r929:
            row['plan'] = r929['plan']
            row['agency'] = r929['agency']
            row['channel'] = CHANNEL_MAP.get(r929['agency'], '')
            row['packages'] = r929['packages']
            row['importer'] = r929['importer'] or '(확인필요)'

        # 대행사가 확인됐는데 통다 계열 3개 표기가 아니면 제외
        if row['agency'] and row['agency'] not in CHANNEL_MAP:
            continue

        result[decl_no] = row
    return result


# --------------------------------------------- 유니패스 화물통관진행정보 → 반입일
def _txt(el, tag: str) -> str:
    """자식 태그의 텍스트 (없으면 빈 문자열)"""
    child = el.find(tag)
    return (child.text or '').strip() if child is not None and child.text else ''


def _fmt_arrival(s: str) -> str:
    """'2026-08-03 15:07:42' / '20260803150742' -> '8/3 15:07' (날짜 형식이 아니면 빈 문자열)

    rlbrDttm 자리에 날짜가 아닌 값(보세운송 도착지 등)이 실려오는 경우가 있어,
    숫자만 뽑기 전에 형식을 먼저 검사한다.
    """
    s = (s or '').strip()
    if not (re.match(r'^\d{4}-\d{2}-\d{2}([ T]\d{2}:\d{2})?', s)
            or re.match(r'^\d{8}(\d{4}|\d{6})?$', s)):
        return ''
    d = re.sub(r'\D', '', s)
    month, day = int(d[4:6]), int(d[6:8])
    if not (1 <= month <= 12 and 1 <= day <= 31):
        return ''
    out = f'{month}/{day}'
    if len(d) >= 12:
        out += f' {d[8:10]}:{d[10:12]}'
    return out


def _query_cargo(param: str, bl_no: str, year: str):
    """유니패스 1회 조회 → 진행이력 엘리먼트 리스트 (조회결과 없으면 None)"""
    qs = urllib.parse.urlencode({'crkyCn': UNIPASS_KEY, 'blYy': year, param: bl_no})
    req = urllib.request.Request(f'{CARGO_API}?{qs}', headers={'User-Agent': 'Mozilla/5.0'})
    with urllib.request.urlopen(req, timeout=20) as resp:
        root = ET.fromstring(resp.read())
    if root.find('cargCsclPrgsInfoQryVo') is None:   # 마스터가 없으면 조회 실패
        return None
    return root.findall('cargCsclPrgsInfoDtlQryVo')


def fetch_arrival(bl_no: str, year: str, warehouse: str) -> str:
    """B/L번호로 '창고 반입신고' 일시를 조회. 미반입·조회실패면 빈 문자열.

    한 건에 반입신고가 여러 번 찍힌다 (부두 CY 반입 → 보세운송 → 보세창고 반입).
    검사는 수입신고서에 기재된 장치장에서 이뤄지므로, 929/5EM의 장치장부호와
    일치하는 반입신고 건만 채택한다 (부두 CY 반입은 제외, 추측 폴백 없음).
    """
    if not warehouse:
        return ''
    details = None
    for yy in (year, str(int(year) - 1)):          # 연말/연초에 B/L연도가 어긋나는 경우 대비
        for param in ('hblNo', 'mblNo'):           # 데이터의 B/L이 H인지 M인지 확실치 않음
            try:
                details = _query_cargo(param, bl_no, yy)
            except Exception as e:
                print(f'  ! {bl_no} 조회 실패 ({param}/{yy}): {e}')
                details = None
            if details:
                break
        if details:
            break
    if not details:
        return ''

    carry_ins = [d for d in details
                 if '반입' in _txt(d, 'cargTrcnRelaBsopTpcd')
                 and _txt(d, 'shedSgn').split('/')[0] == warehouse]
    if not carry_ins:
        return ''                                  # 해당 장치장 반입 전 (부두 CY 반입만 있는 상태 포함)
    picked = max(carry_ins, key=lambda d: _txt(d, 'prcsDttm'))

    # rlbrDttm(실제 반출입일시) 우선, 형식이 깨져 오는 경우가 있어 검증 후 prcsDttm으로 대체
    raw = _txt(picked, 'rlbrDttm')
    if not re.match(r'^\d{4}-\d{2}-\d{2}', raw):
        raw = _txt(picked, 'prcsDttm')
    return _fmt_arrival(raw)


def fill_arrivals(rows: list):
    """반입일이 비어 있는 행만 유니패스로 조회해 채운다 (이미 값이 있으면 건드리지 않음)."""
    if not UNIPASS_KEY:
        print('유니패스 화물API 인증키가 없어 반입일 자동조회를 건너뜁니다 '
              '(config.ini 에 [unipass] cargo_key = ... 추가)')
        return

    # 장치장부호가 있어야 어느 반입신고가 해당 창고 건인지 판별할 수 있다
    cutoff = (datetime.now() - timedelta(days=ARRIVAL_LOOKUP_DAYS)).strftime('%Y-%m-%d')
    targets = [r for r in rows
               if not r.get('arrival') and r.get('hbl') and r.get('warehouse')
               and (r.get('date') or '') >= cutoff]
    if not targets:
        return

    print(f'반입일 조회 대상 {len(targets)}건')
    filled = 0
    for r in targets:
        year = (r.get('date') or '')[:4] or datetime.now().strftime('%Y')
        try:
            got = fetch_arrival(r['hbl'], year, r.get('warehouse') or '')
        except Exception as e:                     # 반입일 때문에 전체 갱신이 죽으면 안 됨
            print(f'  ! {r["hbl"]} 처리 중 오류: {e}')
            got = ''
        if got:
            r['arrival'] = got
            filled += 1
        time.sleep(0.3)                            # 유니패스 연속호출 부하 방지
    print(f'반입일 채움 {filled}건 / 미반입·조회실패 {len(targets) - filled}건')


def fetch_existing_rows() -> dict:
    """이미 게시된 data.json을 읽어 declNo -> row 맵으로 반환 (실패 시 빈 맵)."""
    try:
        req = urllib.request.Request(RAW_URL + '?t=' + str(int(datetime.now().timestamp())))
        with urllib.request.urlopen(req, timeout=15) as resp:
            data = json.loads(resp.read().decode('utf-8'))
        return {r['declNo']: r for r in data.get('rows', [])}
    except Exception as e:
        print(f'기존 data.json 조회 실패 (새로 시작합니다): {e}')
        return {}


def publish(payload: dict):
    if not GH_TOKEN:
        print('GitHub 토큰이 없습니다. config.ini 에 [github] token = ... 을 추가하세요.')
        sys.exit(1)

    body_text = json.dumps(payload, ensure_ascii=False, indent=2)
    content_b64 = base64.b64encode(body_text.encode('utf-8')).decode('ascii')

    sha = None
    try:
        req = urllib.request.Request(API_URL, headers={'Authorization': f'token {GH_TOKEN}'})
        with urllib.request.urlopen(req, timeout=15) as resp:
            sha = json.loads(resp.read().decode('utf-8')).get('sha')
    except urllib.error.HTTPError as e:
        if e.code != 404:
            print(f'기존 파일 조회 중 경고: {e}')

    put_body = {
        'message': f"검사건 리스트 자동 갱신 ({payload['today']}, {payload['totalCount']}건)",
        'content': content_b64,
    }
    if sha:
        put_body['sha'] = sha

    req2 = urllib.request.Request(
        API_URL,
        data=json.dumps(put_body).encode('utf-8'),
        headers={'Authorization': f'token {GH_TOKEN}', 'Content-Type': 'application/json'},
        method='PUT',
    )
    try:
        with urllib.request.urlopen(req2, timeout=15) as resp:
            print(f'게시 완료 (HTTP {resp.status})')
    except urllib.error.HTTPError as e:
        print(f'게시 실패: {e.code} {e.read().decode("utf-8", "ignore")}')
        sys.exit(1)


def main():
    if not RECV_DIR or not os.path.exists(RECV_DIR):
        print(f'recv_dir 접근 불가: {RECV_DIR!r} (config.ini 확인 필요)')
        sys.exit(1)
    if not SEND_DIR or not os.path.exists(SEND_DIR):
        print(f'send_dir 접근 불가: {SEND_DIR!r} (config.ini 확인 필요)')
        sys.exit(1)

    rows5em, rows929, rows023 = scan()
    scanned_rows = build_rows(rows5em, rows929, rows023)

    existing_rows = fetch_existing_rows()

    # 스캔 결과에는 반입일이 비어 있으므로, 이미 게시된 값(자동조회분·수동입력분)을 물려받는다
    for decl_no, row in scanned_rows.items():
        prev = existing_rows.get(decl_no)
        if prev and prev.get('arrival') and not row.get('arrival'):
            row['arrival'] = prev['arrival']

    merged = dict(existing_rows)   # 과거(스캔 범위 밖) 데이터는 그대로 보존
    merged.update(scanned_rows)    # 이번에 스캔된 신고번호만 새로 추가/갱신

    rows = list(merged.values())
    rows.sort(key=lambda r: (r.get('date', ''), r.get('declNo', '')))
    for i, r in enumerate(rows, start=1):
        r['no'] = i

    fill_arrivals(rows)            # 반입일이 비어 있는 행만 유니패스로 조회

    confirmed = sum(1 for r in rows if r.get('verified'))
    payload = {
        'updated': datetime.now().strftime('%Y-%m-%d %H:%M'),
        'today': datetime.now().strftime('%Y-%m-%d'),
        'totalCount': len(rows),
        'autoCount': confirmed,
        'pendingCount': len(rows) - confirmed,
        'rows': rows,
    }

    print(f"스캔 결과: 신규/갱신 {len(scanned_rows)}건, 전체 {len(rows)}건 "
          f"(확정 {confirmed} / 5EM대기 {len(rows) - confirmed})")
    publish(payload)


if __name__ == '__main__':
    main()
