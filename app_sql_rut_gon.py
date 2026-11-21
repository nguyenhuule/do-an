# Stockly — ứng dụng quản lý kho bằng Streamlit và SQLite.
# Bản rút gọn từ app_sql.py: giữ nguyên logic/chức năng, bỏ docstring và khoảng trắng dư.

import io

import math

import base64

import pandas as pd

import streamlit as st

import json

import sqlite3

from contextlib import contextmanager

import hashlib

import hmac

import secrets

import time

import os

import re

import unicodedata

from html import escape as _esc

from datetime import datetime

import tempfile

from pathlib import Path

import streamlit.components.v1 as components

# ============ CẤU HÌNH CHUNG ============

MAX_HANG = 10

MAX_COT = 10

SO_VI_TRI = 5

MAX_VI_TRI = 20

MAX_KE = 9

STT_MAX = 999

FILE_DB = 'kho.db'

# --- Các file JSON CŨ: chỉ còn dùng để chuyển dữ liệu sang SQL ở lần chạy đầu ---

FILE_DATA = 'kho_data.json'

FILE_LICH_SU = 'lich_su_kho.json'

THU_MUC_DU_LIEU = 'du_lieu_tai_khoan'

FILE_TAI_KHOAN = 'tai_khoan.json'

MK_TOI_THIEU = 6

SAI_TOI_DA = 5

KHOA_GIAY = 30

FILE_PHIEN = 'phien_dang_nhap.json'

COOKIE_PHIEN = 'kho_phien'

PHIEN_NGAY = 30

# ============ LOGO ============

FILE_LOGO = Path(__file__).with_name('logo.png')

def _mo_logo():
    try:
        from PIL import Image
        return Image.open(FILE_LOGO)
    except Exception:
        return None

@st.cache_resource(show_spinner=False)
def _logo_data_uri(cao_px):
    im = _mo_logo()
    if im is None:
        return ''
    im = im.convert('RGBA')
    rong = max(1, round(im.width * cao_px / im.height))
    im = im.resize((rong, cao_px))
    buf = io.BytesIO()
    im.save(buf, format='PNG', optimize=True)
    return 'data:image/png;base64,' + base64.b64encode(buf.getvalue()).decode('ascii')

def html_logo(cao_css, kieu=''):
    uri = _logo_data_uri(int(cao_css * 2))
    if not uri:
        return ''
    return f'<img src="{uri}" alt="Stockly" style="height:{cao_css}px;width:auto;{kieu}">'

st.set_page_config(page_title='Stockly - Quản lý kho hàng', page_icon=_mo_logo() or '', layout='wide')

# ============ CHUẨN HÓA CHUỖI CHO MÃ SẢN PHẨM ============

def chuan_hoa(chuoi):
    chuoi = chuoi.strip()
    chuoi = unicodedata.normalize('NFD', chuoi)
    chuoi = ''.join((ch for ch in chuoi if unicodedata.category(ch) != 'Mn'))
    chuoi = chuoi.replace('đ', 'd').replace('Đ', 'D')
    chuoi = re.sub('[^A-Za-z0-9]', '', chuoi)
    return chuoi.upper()

def ma_hop_le(chuoi):
    return len(chuan_hoa(chuoi or '')) == 3

# ============ HÀM XỬ LÝ DỮ LIỆU ============

def tao_kho_rong():
    return {}

def tao_ke_rong(so_hang, so_cot, so_vi_tri=SO_VI_TRI):
    return [[[None for _ in range(so_vi_tri)] for _ in range(so_cot)] for _ in range(so_hang)]

# ============ CƠ SỞ DỮ LIỆU SQL (SQLite) ============

SCHEMA = """
CREATE TABLE IF NOT EXISTS tai_khoan (
    ten       TEXT PRIMARY KEY,            -- phân biệt chữ hoa / chữ thường (so sánh nhị phân)
    muoi      TEXT NOT NULL,
    mat_khau  TEXT NOT NULL,               -- PBKDF2-SHA256 + muối
    ngay_tao  TEXT NOT NULL
);
CREATE TABLE IF NOT EXISTS ke (
    tai_khoan TEXT NOT NULL REFERENCES tai_khoan(ten) ON DELETE CASCADE,
    ten_ke    TEXT NOT NULL,
    so_hang   INTEGER NOT NULL,
    so_cot    INTEGER NOT NULL,
    so_vi_tri INTEGER NOT NULL,
    PRIMARY KEY (tai_khoan, ten_ke)
);
CREATE TABLE IF NOT EXISTS vi_tri (        -- chỉ lưu các vị trí ĐANG CÓ HÀNG; vị trí trống = không có dòng
    tai_khoan TEXT NOT NULL,
    ten_ke    TEXT NOT NULL,
    hang      INTEGER NOT NULL,
    cot       INTEGER NOT NULL,
    vt        INTEGER NOT NULL,
    ten_hang  TEXT NOT NULL,
    loai      TEXT NOT NULL,
    stt       INTEGER NOT NULL,
    PRIMARY KEY (tai_khoan, ten_ke, hang, cot, vt),
    FOREIGN KEY (tai_khoan, ten_ke) REFERENCES ke(tai_khoan, ten_ke) ON DELETE CASCADE
);
CREATE TABLE IF NOT EXISTS lich_su (
    id          INTEGER PRIMARY KEY AUTOINCREMENT,
    tai_khoan   TEXT NOT NULL REFERENCES tai_khoan(ten) ON DELETE CASCADE,
    thoi_gian   TEXT NOT NULL,
    hanh_dong   TEXT NOT NULL,
    ma_san_pham TEXT,
    ten_hang    TEXT,
    loai        TEXT
);
CREATE INDEX IF NOT EXISTS idx_lich_su_tk ON lich_su(tai_khoan, id);
CREATE TABLE IF NOT EXISTS phien (
    ma_bam  TEXT PRIMARY KEY,              -- SHA-256 của mã phiên (mã gốc chỉ nằm trong cookie)
    ten     TEXT NOT NULL REFERENCES tai_khoan(ten) ON DELETE CASCADE,
    het_han REAL NOT NULL
);
CREATE TABLE IF NOT EXISTS meta (khoa TEXT PRIMARY KEY, gia_tri TEXT);
"""

SCHEMA_TEN_SAN_PHAM = """
CREATE TABLE IF NOT EXISTS ten_san_pham (  -- mã sản phẩm (dùng trong mã QR) -> tên sản phẩm (hiển thị)
    tai_khoan TEXT NOT NULL REFERENCES tai_khoan(ten) ON DELETE CASCADE,
    viet_tat  TEXT NOT NULL,                -- đã chuẩn hóa (viết hoa, bỏ dấu, bỏ khoảng trắng) như trong mã
    day_du    TEXT NOT NULL,
    PRIMARY KEY (tai_khoan, viet_tat)
);
CREATE TABLE IF NOT EXISTS loai_san_pham (  -- (mã sản phẩm, mã loại) dùng trong mã QR -> tên loại (hiển thị)
    tai_khoan TEXT NOT NULL REFERENCES tai_khoan(ten) ON DELETE CASCADE,
    ma_sp     TEXT NOT NULL,                -- mã sản phẩm đã chuẩn hóa
    ma_loai   TEXT NOT NULL,                -- mã loại đã chuẩn hóa
    ten_loai  TEXT NOT NULL,
    PRIMARY KEY (tai_khoan, ma_sp, ma_loai)
);
"""

SCHEMA_KHOI_PHUC = """
CREATE TABLE IF NOT EXISTS khoi_phuc (      -- mã khôi phục mật khẩu: chỉ lưu BẢN BĂM (PBKDF2 + muối), không lưu mã gốc
    ten      TEXT PRIMARY KEY REFERENCES tai_khoan(ten) ON DELETE CASCADE,
    muoi     TEXT NOT NULL,
    ma_bam   TEXT NOT NULL,
    sai      INTEGER NOT NULL DEFAULT 0,    -- số lần nhập sai mã liên tiếp
    khoa_den REAL NOT NULL DEFAULT 0        -- đang bị tạm khóa đến thời điểm này (time.time())
);
"""

SCHEMA = SCHEMA + SCHEMA_TEN_SAN_PHAM + SCHEMA_KHOI_PHUC

PHIEN_BAN_SCHEMA = 5

def _doc_json(duong_dan, mac_dinh):
    try:
        with open(duong_dan, 'r', encoding='utf-8') as f:
            return json.load(f)
    except (OSError, ValueError):
        return mac_dinh

def _chuyen_json_sang_sql(con):
    ds = _doc_json(FILE_TAI_KHOAN, {})
    if not isinstance(ds, dict):
        ds = {}
    ten_dau = None
    for khoa, tk in ds.items():
        if not isinstance(tk, dict):
            continue
        thu_muc = tk.get('thu_muc') or 'tk_' + khoa
        ten = tk.get('hien_thi', khoa)
        if not tk.get('muoi') or not tk.get('mat_khau'):
            continue
        ten_dau = ten_dau or ten
        con.execute('INSERT OR IGNORE INTO tai_khoan(ten, muoi, mat_khau, ngay_tao) VALUES (?,?,?,?)', (ten, tk['muoi'], tk['mat_khau'], tk.get('ngay_tao') or datetime.now().strftime('%Y-%m-%d %H:%M:%S')))
        p_kho = Path(THU_MUC_DU_LIEU) / thu_muc / FILE_DATA
        p_ls = Path(THU_MUC_DU_LIEU) / thu_muc / FILE_LICH_SU
        if ten == ten_dau:
            if not p_kho.exists() and Path(FILE_DATA).exists():
                p_kho = Path(FILE_DATA)
            if not p_ls.exists() and Path(FILE_LICH_SU).exists():
                p_ls = Path(FILE_LICH_SU)
        kho = _doc_json(p_kho, {})
        if isinstance(kho, dict):
            _ghi_kho(con, ten, kho)
        ls = _doc_json(p_ls, [])
        if isinstance(ls, list):
            con.executemany('INSERT INTO lich_su(tai_khoan, thoi_gian, hanh_dong, ma_san_pham, ten_hang, loai) VALUES (?,?,?,?,?,?)', [(ten, m.get('thoi_gian', ''), m.get('hanh_dong', ''), m.get('ma_san_pham'), m.get('ten_hang'), m.get('loai')) for m in ls if isinstance(m, dict)])
    phien = _doc_json(FILE_PHIEN, {})
    if isinstance(phien, dict):
        for ma_bam, m in phien.items():
            if isinstance(m, dict) and m.get('ten') and (m.get('het_han', 0) > time.time()):
                con.execute('INSERT OR IGNORE INTO phien(ma_bam, ten, het_han) SELECT ?, ?, ? WHERE EXISTS (SELECT 1 FROM tai_khoan WHERE ten = ?)', (ma_bam, m['ten'], m['het_han'], m['ten']))

@st.cache_resource
def _khoi_tao_db(phien_ban=PHIEN_BAN_SCHEMA):
    con = sqlite3.connect(FILE_DB, timeout=30)
    try:
        con.execute('PRAGMA journal_mode = WAL')
        con.execute('PRAGMA foreign_keys = ON')
        with con:
            con.executescript(SCHEMA)
            da_chuyen = con.execute("SELECT 1 FROM meta WHERE khoa = 'da_chuyen_json'").fetchone()
            if not da_chuyen:
                _chuyen_json_sang_sql(con)
                con.execute("INSERT INTO meta(khoa, gia_tri) VALUES ('da_chuyen_json', '1')")
    finally:
        con.close()
    return True

@contextmanager
def _db():
    _khoi_tao_db()
    con = sqlite3.connect(FILE_DB, timeout=30)
    con.row_factory = sqlite3.Row
    con.execute('PRAGMA foreign_keys = ON')
    try:
        with con:
            yield con
    finally:
        con.close()

# ---------- Tài khoản ----------

def lay_tai_khoan(ten):
    with _db() as con:
        r = con.execute('SELECT ten, muoi, mat_khau, ngay_tao FROM tai_khoan WHERE ten = ?', (ten,)).fetchone()
    return dict(r) if r else None

def them_tai_khoan(ten, muoi, mat_khau_bam):
    try:
        with _db() as con:
            con.execute('INSERT INTO tai_khoan(ten, muoi, mat_khau, ngay_tao) VALUES (?,?,?,?)', (ten, muoi, mat_khau_bam, datetime.now().strftime('%Y-%m-%d %H:%M:%S')))
        return True
    except sqlite3.IntegrityError:
        return False

# ---------- Mã khôi phục mật khẩu ----------

KP_KY_TU = 'ABCDEFGHJKLMNPQRSTUVWXYZ23456789'

KP_DO_DAI = 12

KP_SAI_TOI_DA = 5

KP_KHOA_GIAY = 300

def _chuan_ma_kp(ma):
    return re.sub('[^A-Z0-9]', '', (ma or '').upper())

def co_ma_khoi_phuc(ten):
    with _db() as con:
        return con.execute('SELECT 1 FROM khoi_phuc WHERE ten = ?', (ten,)).fetchone() is not None

def tao_ma_khoi_phuc(ten):
    ma = ''.join((secrets.choice(KP_KY_TU) for _ in range(KP_DO_DAI)))
    muoi = secrets.token_hex(16)
    bam = bam_mat_khau(ma, muoi)
    with _db() as con:
        con.execute('INSERT OR REPLACE INTO khoi_phuc(ten, muoi, ma_bam, sai, khoa_den) VALUES (?,?,?,0,0)', (ten, muoi, bam))
    return f'{ma[:4]}-{ma[4:8]}-{ma[8:]}'

def dat_lai_mat_khau_bang_ma(ten, ma, mat_khau_moi, nhap_lai):
    ten, ma = ((ten or '').strip(), _chuan_ma_kp(ma))
    if not ten or not ma:
        return (False, 'Vui lòng nhập tên tài khoản và mã khôi phục.')
    if len(mat_khau_moi or '') < MK_TOI_THIEU:
        return (False, f'Mật khẩu mới phải có ít nhất {MK_TOI_THIEU} ký tự.')
    if mat_khau_moi != nhap_lai:
        return (False, 'Hai lần nhập mật khẩu mới không giống nhau.')
    loi_chung = 'Tên tài khoản hoặc mã khôi phục không đúng.'
    with _db() as con:
        r = con.execute('SELECT muoi, ma_bam, sai, khoa_den FROM khoi_phuc WHERE ten = ?', (ten,)).fetchone()
        if r is not None and r['khoa_den'] > time.time():
            return (False, f"Nhập sai quá nhiều lần. Vui lòng thử lại sau {int(r['khoa_den'] - time.time()) // 60 + 1} phút.")
        bam = bam_mat_khau(ma, r['muoi'] if r else '00' * 16)
        if r is None or not hmac.compare_digest(bam, r['ma_bam']):
            if r is not None:
                sai = r['sai'] + 1
                khoa = time.time() + KP_KHOA_GIAY if sai >= KP_SAI_TOI_DA else 0
                con.execute('UPDATE khoi_phuc SET sai = ?, khoa_den = ? WHERE ten = ?', (0 if khoa else sai, khoa, ten))
            return (False, loi_chung)
        muoi_moi = secrets.token_hex(16)
        con.execute('UPDATE tai_khoan SET muoi = ?, mat_khau = ? WHERE ten = ?', (muoi_moi, bam_mat_khau(mat_khau_moi, muoi_moi), ten))
        con.execute('DELETE FROM phien WHERE ten = ?', (ten,))
    return (True, tao_ma_khoi_phuc(ten))

def _ten_khoa(ten=None):
    ten = (ten or st.session_state.get('nguoi_dung') or '').strip()
    if not re.fullmatch('[A-Za-z0-9_.\\-]{3,30}', ten):
        raise PermissionError('Chưa đăng nhập: không có kho dữ liệu để đọc / ghi.')
    if lay_tai_khoan(ten) is None:
        raise PermissionError('Tài khoản không tồn tại.')
    return ten

# ---------- Kho hàng ----------

def _ghi_kho(con, ten, kho):
    con.execute('DELETE FROM ke WHERE tai_khoan = ?', (ten,))
    for ten_ke, ke in kho.items():
        so_hang = len(ke)
        so_cot = len(ke[0]) if so_hang else 0
        so_vt = len(ke[0][0]) if so_cot else 0
        con.execute('INSERT INTO ke(tai_khoan, ten_ke, so_hang, so_cot, so_vi_tri) VALUES (?,?,?,?,?)', (ten, ten_ke, so_hang, so_cot, so_vt))
        con.executemany('INSERT INTO vi_tri(tai_khoan, ten_ke, hang, cot, vt, ten_hang, loai, stt) VALUES (?,?,?,?,?,?,?,?)', [(ten, ten_ke, h, c, i, v['ten_hang'], v['loai'], int(v['stt'])) for h, hang in enumerate(ke) for c, o in enumerate(hang) for i, v in enumerate(o) if v is not None])

def doc_du_lieu(ten=None):
    ten = _ten_khoa(ten)
    kho = tao_kho_rong()
    with _db() as con:
        for r in con.execute('SELECT ten_ke, so_hang, so_cot, so_vi_tri FROM ke WHERE tai_khoan = ? ORDER BY rowid', (ten,)):
            kho[r['ten_ke']] = tao_ke_rong(r['so_hang'], r['so_cot'], r['so_vi_tri'])
        for r in con.execute('SELECT ten_ke, hang, cot, vt, ten_hang, loai, stt FROM vi_tri WHERE tai_khoan = ?', (ten,)):
            kho[r['ten_ke']][r['hang']][r['cot']][r['vt']] = {'ten_hang': r['ten_hang'], 'loai': r['loai'], 'stt': r['stt']}
    return kho

def luu_du_lieu(kho):
    ten = _ten_khoa()
    with _db() as con:
        _ghi_kho(con, ten, kho)

def _dinh_dang_stt_trong_ma(ma):
    ma = re.sub('^(K\\d+)T\\d+-', '\\1-', str(ma))
    return re.sub('-(\\d+)$', lambda m: f'-{int(m.group(1)):03d}', ma)

# ---------- Lịch sử nhập / xuất ----------

def doc_lich_su():
    ten = _ten_khoa()
    with _db() as con:
        rows = con.execute('SELECT thoi_gian, hanh_dong, ma_san_pham, ten_hang, loai FROM lich_su WHERE tai_khoan = ? ORDER BY id', (ten,)).fetchall()
    lich_su = [dict(r) for r in rows]
    for muc in lich_su:
        if muc.get('ma_san_pham'):
            muc['ma_san_pham'] = _dinh_dang_stt_trong_ma(muc['ma_san_pham'])
    return lich_su

def ghi_lich_su(hanh_dong, ma_sp, ten_hang, loai):
    ten = _ten_khoa()
    with _db() as con:
        con.execute('INSERT INTO lich_su(tai_khoan, thoi_gian, hanh_dong, ma_san_pham, ten_hang, loai) VALUES (?,?,?,?,?,?)', (ten, datetime.now().strftime('%Y-%m-%d %H:%M:%S'), hanh_dong, ma_sp, ten_hang, loai))

# ---------- Tên sản phẩm của sản phẩm (mã sản phẩm trong mã QR -> tên sản phẩm để hiển thị) ----------

def luu_ten_day_du(cac_cap):
    cac_cap = [(chuan_hoa(vt), dd.strip()) for vt, dd in cac_cap if chuan_hoa(vt) and dd and dd.strip()]
    if not cac_cap:
        return
    ten = _ten_khoa()
    with _db() as con:
        con.executescript(SCHEMA_TEN_SAN_PHAM)
        con.executemany('INSERT INTO ten_san_pham(tai_khoan, viet_tat, day_du) VALUES (?,?,?) ON CONFLICT(tai_khoan, viet_tat) DO UPDATE SET day_du = excluded.day_du', [(ten, vt, dd) for vt, dd in cac_cap])

def doc_ten_day_du():
    with _db() as con:
        con.executescript(SCHEMA_TEN_SAN_PHAM)
        return {r['viet_tat']: r['day_du'] for r in con.execute('SELECT viet_tat, day_du FROM ten_san_pham WHERE tai_khoan = ?', (_ten_khoa(),))}

def ten_day_du(ten_hang, bang=None):
    if bang is None:
        bang = doc_ten_day_du()
    return bang.get(chuan_hoa(ten_hang), ten_hang)

def luu_ten_loai_day_du(cac_bo):
    cac_bo = [(chuan_hoa(sp), chuan_hoa(lo), tl.strip()) for sp, lo, tl in cac_bo if chuan_hoa(sp) and chuan_hoa(lo) and tl and tl.strip()]
    if not cac_bo:
        return
    ten = _ten_khoa()
    with _db() as con:
        con.executescript(SCHEMA_TEN_SAN_PHAM)
        con.executemany('INSERT INTO loai_san_pham(tai_khoan, ma_sp, ma_loai, ten_loai) VALUES (?,?,?,?) ON CONFLICT(tai_khoan, ma_sp, ma_loai) DO UPDATE SET ten_loai = excluded.ten_loai', [(ten, sp, lo, tl) for sp, lo, tl in cac_bo])

def doc_ten_loai_day_du():
    with _db() as con:
        con.executescript(SCHEMA_TEN_SAN_PHAM)
        return {(r['ma_sp'], r['ma_loai']): r['ten_loai'] for r in con.execute('SELECT ma_sp, ma_loai, ten_loai FROM loai_san_pham WHERE tai_khoan = ?', (_ten_khoa(),))}

def ten_loai_day_du(ten_hang, loai, bang=None):
    if bang is None:
        bang = doc_ten_loai_day_du()
    return bang.get((chuan_hoa(ten_hang), chuan_hoa(loai)), loai)

# ============ GHI NHỚ ĐĂNG NHẬP (sống sót khi tải lại trang) ============

def _bam_phien(ma):
    return hashlib.sha256(ma.encode('utf-8')).hexdigest()

def tao_phien(ten):
    now = time.time()
    ma = secrets.token_urlsafe(32)
    with _db() as con:
        con.execute('DELETE FROM phien WHERE het_han <= ?', (now,))
        con.execute('INSERT INTO phien(ma_bam, ten, het_han) VALUES (?,?,?)', (_bam_phien(ma), ten, now + PHIEN_NGAY * 86400))
    return ma

def tim_phien(ma):
    if not ma:
        return None
    with _db() as con:
        r = con.execute('SELECT ten FROM phien WHERE ma_bam = ? AND het_han > ?', (_bam_phien(ma), time.time())).fetchone()
    return r['ten'] if r else None

def huy_phien(ma):
    if not ma:
        return
    with _db() as con:
        con.execute('DELETE FROM phien WHERE ma_bam = ?', (_bam_phien(ma),))

def _cookie_hien_tai():
    try:
        ma = st.context.cookies.get(COOKIE_PHIEN)
        return ma if isinstance(ma, str) and ma else None
    except Exception:
        return None

def _js_cookie(ma=None):
    if ma:
        lenh = f'{COOKIE_PHIEN}={ma}; path=/; max-age={PHIEN_NGAY * 86400}; SameSite=Lax'
    else:
        lenh = f'{COOKIE_PHIEN}=; path=/; max-age=0; SameSite=Lax'
    components.html(f'<script>window.parent.document.cookie = {json.dumps(lenh)};</script>', height=0)

# ============ KHỞI TẠO SESSION STATE ============

if st.session_state.get('nguoi_dung') and 'kho' not in st.session_state:
    try:
        st.session_state.kho = doc_du_lieu()
    except PermissionError:
        st.session_state.clear()

if 'chuc_nang' not in st.session_state:
    st.session_state.chuc_nang = None

def co_ke():
    return len(st.session_state.kho) > 0

def ke_dang_dung(ten_ke):
    return sum((1 for hang in st.session_state.kho[ten_ke] for o in hang for vt in o if vt is not None))

def xoa_ke(ten_ke):
    if ten_ke not in st.session_state.kho or ke_dang_dung(ten_ke) > 0:
        return False
    del st.session_state.kho[ten_ke]
    luu_du_lieu(st.session_state.kho)
    for k in ('nhap_ke', 'xuat_ke', 'kt_ke'):
        if st.session_state.get(k) == ten_ke:
            for kk in (k, k.replace('_ke', '_hang'), k.replace('_ke', '_cot')):
                st.session_state.pop(kk, None)
    for k in ('nhap_o', 'kt_qr_o'):
        o = st.session_state.get(k)
        if o is not None and o[0] == ten_ke:
            st.session_state.pop(k, None)
    return True

def so_ke_tiep_theo():
    da_dung = {lay_so_ke(k) for k in st.session_state.kho}
    return next((n for n in range(1, MAX_KE + 1) if n not in da_dung), None)

def them_ke(so_hang, so_cot, so_vi_tri=SO_VI_TRI):
    so = so_ke_tiep_theo()
    if so is None:
        raise ValueError(f'Đã đủ {MAX_KE} kệ (mã kệ chỉ có 2 ký tự: K1 đến K{MAX_KE}).')
    ten_ke = f'Kệ {so}'
    st.session_state.kho[ten_ke] = tao_ke_rong(int(so_hang), int(so_cot), int(so_vi_tri))
    luu_du_lieu(st.session_state.kho)
    return ten_ke

def kiem_tra_sua_ke(ten_ke, so_hang, so_cot, so_vt):
    ke = st.session_state.kho[ten_ke]
    cu_hang, cu_cot, cu_vt = (len(ke), len(ke[0]), len(ke[0][0]))
    vuong = {'hang': [], 'cot': [], 'vt': []}
    for h in range(cu_hang):
        for c in range(cu_cot):
            o = ke[h][c]
            if h >= so_hang:
                if any((vt is not None for vt in o)):
                    vuong['hang'].append(ma_o(ten_ke, h, c))
            elif c >= so_cot:
                if any((vt is not None for vt in o)):
                    vuong['cot'].append(ma_o(ten_ke, h, c))
            elif so_vt < cu_vt and any((vt is not None for vt in o[so_vt:])):
                vuong['vt'].append(ma_o(ten_ke, h, c))

    def liet_ke(ds):
        return ', '.join(ds[:8]) + (f' và {len(ds) - 8} ô khác' if len(ds) > 8 else '')
    ly_do = []
    if vuong['hang']:
        ly_do.append(f"Các tầng từ {so_hang + 1} trở lên còn hàng ở: {liet_ke(vuong['hang'])}.")
    if vuong['cot']:
        ly_do.append(f"Các cột từ {so_cot + 1} trở lên còn hàng ở: {liet_ke(vuong['cot'])}.")
    if vuong['vt']:
        ly_do.append(f"Vị trí từ {so_vt + 1} trở lên còn hàng ở: {liet_ke(vuong['vt'])}.")
    return ly_do

def sua_ke(ten_ke, so_hang, so_cot, so_vt):
    if ten_ke not in st.session_state.kho:
        return (False, 'Kệ không tồn tại.')
    so_hang, so_cot, so_vt = (int(so_hang), int(so_cot), int(so_vt))
    ly_do = kiem_tra_sua_ke(ten_ke, so_hang, so_cot, so_vt)
    if ly_do:
        return (False, ' '.join(ly_do))
    cu = st.session_state.kho[ten_ke]
    moi = tao_ke_rong(so_hang, so_cot, so_vt)
    for h in range(min(so_hang, len(cu))):
        for c in range(min(so_cot, len(cu[0]))):
            for i in range(min(so_vt, len(cu[h][c]))):
                moi[h][c][i] = cu[h][c][i]
    st.session_state.kho[ten_ke] = moi
    luu_du_lieu(st.session_state.kho)
    for k in ('nhap_ke', 'xuat_ke', 'kt_ke'):
        if st.session_state.get(k) == ten_ke:
            for kk in (k.replace('_ke', '_hang'), k.replace('_ke', '_cot')):
                st.session_state.pop(kk, None)
    return (True, '')

# ============ SINH MÃ Ô & MÃ SẢN PHẨM ============

def lay_so_ke(ten_ke):
    return int(ten_ke.replace('Kệ', '').strip())

def ma_o(ten_ke, h, c):
    so_ke = lay_so_ke(ten_ke)
    return f'K{so_ke}T{h + 1}{c + 1:02d}'

def ma_san_pham_tu_so_ke(so_ke, ten_hang, loai, stt):
    return f'K{so_ke}-{chuan_hoa(ten_hang)}-{chuan_hoa(loai)}-{stt:03d}'

def ma_san_pham(ten_ke, h, c, ten_hang, loai, stt):
    return ma_san_pham_tu_so_ke(lay_so_ke(ten_ke), ten_hang, loai, stt)

# ============ GIAO DIỆN ============

CSS_CHUNG = """
<style>
@import url('https://fonts.googleapis.com/css2?family=Barlow+Condensed:wght@500;600;700&family=Barlow+Semi+Condensed:wght@400;500;600;700&display=swap');
:root{
  --nen:#F7F5F0;   /* màu nền trang: be nhạt */
  --bg:#e9ebee; --paper:#f8f9fa; --ink:#14181f; --muted:#5a6270; --line:#c5cbd4; --slot:#d3d8df;
  --rack:#1a3c9c; --on-rack:#ffffff; --rack-dark:#12296e; --rack-tint:#dfe6f7; --beam:#ee7a14;
  --bad:#b3261e; --bad-tint:#f6dcd9;
  --tc:#0f766e; --tc-dark:#0a5750; --on-tc:#ffffff;      /* Tra cứu: xanh ngọc */
  --tl:#6d3fb8; --tl-dark:#522e8c; --on-tl:#ffffff;      /* Thiết lập: tím */
  --f-ui:'Barlow Semi Condensed','Segoe UI',Roboto,'Helvetica Neue',sans-serif;
  --f-head:'Barlow Condensed','Arial Narrow','Segoe UI',sans-serif;
}
@media (prefers-color-scheme: dark){
  :root{
    --nen:#0f1218;
    --bg:#0f1218; --paper:#171b23; --ink:#e7eaef; --muted:#97a0ad; --line:#2f3643; --slot:#2a303b;
    --rack:#86a2ff; --on-rack:#0b1226; --rack-dark:#a9bdff; --rack-tint:#1b2440; --beam:#f28b2d;
    --bad:#ff8a80; --bad-tint:#3b1d1b;
    --tc:#5fd6c8; --tc-dark:#8fe6dc; --on-tc:#06201d;
    --tl:#c2a6f5; --tl-dark:#d9c8fa; --on-tl:#1a0f33;
  }
}
.stApp, [data-testid="stAppViewContainer"]{ background:var(--nen) !important; }
.stApp{ color:var(--ink); }
.stApp, .stApp p, .stApp label, .stApp li, .stApp td, .stApp th, .stApp input, .stApp textarea, .stApp button, .stApp select,
.stApp [data-baseweb], .stApp [data-testid="stCaptionContainer"]{ font-family:var(--f-ui); }
.stApp span[data-testid="stIconMaterial"]{ font-family:"Material Symbols Rounded" !important; }
[data-testid="stMarkdownContainer"] p{ font-size:1.05rem; }
[data-testid="stHeader"]{ background:transparent !important; }
[data-testid="stMainBlockContainer"], .block-container{ max-width:1180px; margin:0 auto; padding-top:2.4rem; }
div[data-testid="stElementContainer"]:has(> div[data-testid="stMarkdownContainer"] > style),
div.element-container:has(> div[data-testid="stMarkdownContainer"] > style){ display:none; }
h1,h2,h3,h4,h5{ font-family:var(--f-head); font-weight:600; letter-spacing:0; color:var(--ink); }
h5{ font-size:1.35rem; }
[data-testid="stWidgetLabel"] p, label p{ color:var(--ink); font-weight:500; }
[data-testid="stCaptionContainer"]{ color:var(--muted); }
[data-testid="stMarkdownContainer"] hr, hr{ border:0; border-top:1px solid var(--line); }
:focus-visible{ outline:2px solid var(--rack); outline-offset:2px; }

/* ---- tiêu đề trang ---- */
.pg-head{ display:flex; align-items:baseline; justify-content:space-between; gap:16px; flex-wrap:wrap;
  border-bottom:2px solid var(--ink); padding-bottom:10px; margin:0 0 20px; }
.pg-title{ font:600 clamp(1.7rem,5vw,2.6rem)/1.1 var(--f-head); color:var(--ink); }
.pg-meta{ color:var(--muted); font-size:1rem; }
.pg-head.nho{ padding-bottom:6px; margin-bottom:12px; border-bottom-width:1px; }
.pg-head.nho .pg-title{ font-size:clamp(1.3rem,4vw,1.7rem); }
.sec{ margin:22px 0 8px; font:600 1.2rem/1.2 var(--f-head); color:var(--ink); }

/* ---- dải số liệu (một khối liền, ngăn bằng đường kẻ) ---- */
.strip{ display:grid; grid-template-columns:repeat(4,1fr); border:1px solid var(--line); background:var(--paper);
  border-radius:8px; margin:0 0 22px; }
.strip > div{ padding:14px 18px 16px; border-left:1px solid var(--line); min-width:0; }
.strip > div:first-child{ border-left:0; }
.strip .v{ display:block; font:600 2.1rem/1 var(--f-head); font-variant-numeric:tabular-nums; color:var(--ink); }
.strip .v small{ font-size:1.05rem; font-weight:500; color:var(--muted); }
.strip .k{ display:block; margin-top:7px; color:var(--ink); font-size:.95rem; font-weight:500; }
.ico{ width:18px; height:18px; flex:none; vertical-align:-3px; margin-right:8px; }
.ico.c-blue{ color:var(--rack); } .ico.c-green{ color:var(--tc); }
.ico.c-orange{ color:var(--beam); } .ico.c-violet{ color:var(--tl); }
.pg-title .ico-img{ height:30px; width:auto; vertical-align:-6px; margin-right:10px; }
.pg-title .ico{ width:26px; height:26px; vertical-align:-4px; margin-right:10px; }
.strip .s{ display:block; margin-top:1px; color:var(--muted); font-size:.85rem; }
.strip .bar{ height:4px; background:var(--slot); margin-top:10px; border-radius:2px; overflow:hidden; }
.strip .bar i{ display:block; height:100%; background:var(--rack); }
.canh-bao{ border-left:4px solid var(--bad); background:var(--bad-tint); color:var(--ink); padding:10px 14px;
  border-radius:0 6px 6px 0; margin:-8px 0 20px; font-weight:500; }
@media (max-width:700px){
  .strip{ grid-template-columns:repeat(2,1fr); }
  .strip > div:nth-child(odd){ border-left:0; }
  .strip > div:nth-child(n+3){ border-top:1px solid var(--line); }
}

/* ---- nút ---- */
div[data-testid="stButton"] > button, div[data-testid="stDownloadButton"] > button, div[data-testid="stFormSubmitButton"] > button{
  min-height:44px; border-radius:6px; font-weight:600; background-color:var(--paper); color:var(--ink);
  border:1px solid var(--line); box-shadow:none; transition:background-color .12s, border-color .12s;
}
div[data-testid="stButton"] > button p, div[data-testid="stDownloadButton"] > button p, div[data-testid="stFormSubmitButton"] > button p{
  color:inherit; font-weight:600; font-size:1.04rem; }
div[data-testid="stButton"] > button:hover, div[data-testid="stDownloadButton"] > button:hover, div[data-testid="stFormSubmitButton"] > button:hover{
  border-color:var(--ink); background-color:var(--bg); color:var(--ink); }
div[data-testid="stButton"] > button:disabled{ opacity:.45; }
div[data-testid="stButton"] > button[kind^="primary"], div[data-testid="stButton"] > button[data-testid^="stBaseButton-primary"],
div[data-testid="stDownloadButton"] > button[kind^="primary"], div[data-testid="stDownloadButton"] > button[data-testid^="stBaseButton-primary"],
div[data-testid="stFormSubmitButton"] > button[kind^="primary"], div[data-testid="stFormSubmitButton"] > button[data-testid^="stBaseButton-primary"]{
  background-color:var(--rack); color:var(--on-rack); border-color:var(--rack); }
div[data-testid="stButton"] > button[kind^="primary"]:hover, div[data-testid="stButton"] > button[data-testid^="stBaseButton-primary"]:hover,
div[data-testid="stDownloadButton"] > button[kind^="primary"]:hover, div[data-testid="stDownloadButton"] > button[data-testid^="stBaseButton-primary"]:hover,
div[data-testid="stFormSubmitButton"] > button[kind^="primary"]:hover, div[data-testid="stFormSubmitButton"] > button[data-testid^="stBaseButton-primary"]:hover{
  background-color:var(--rack-dark); color:var(--on-rack); border-color:var(--rack-dark); }
.st-key-dang_xuat button{ min-height:36px !important; }

/* ---- ô nhập, tab, thông báo, form, bảng ---- */
div[data-baseweb="input"], div[data-baseweb="base-input"], div[data-baseweb="textarea"], div[data-baseweb="select"] > div{
  border-radius:6px !important; }
div[data-baseweb="input"], div[data-baseweb="textarea"], div[data-baseweb="select"] > div{
  background-color:var(--paper) !important; border-color:var(--line) !important; }
div[data-baseweb="tab-list"]{ gap:4px; border-bottom:1px solid var(--line); }
div[data-baseweb="tab-border"]{ background:transparent !important; }
button[data-baseweb="tab"]{ border-radius:0; font-weight:600; padding:8px 14px; color:var(--muted); }
button[data-baseweb="tab"][aria-selected="true"]{ color:var(--ink); }
div[data-baseweb="tab-highlight"]{ background-color:var(--rack) !important; height:3px; }
div[data-testid="stAlert"]{ border-radius:6px; box-shadow:none; border:1px solid var(--line); }
.st-key-xoa_ke_loi div[data-testid="stAlert"]{ background:var(--bad-tint); border-color:var(--bad); }
.st-key-xoa_ke_loi div[data-testid="stAlert"] *{ color:var(--bad) !important; }
div[data-testid="stForm"]{ background:var(--paper); border:1px solid var(--line); border-radius:8px; padding:18px; }
div[data-testid="stExpander"] details{ border-radius:8px; border:1px solid var(--line); background:var(--paper); }
div[data-testid="stDataFrame"]{ border-radius:8px; overflow:hidden; border:1px solid var(--line); }

/* ---- sơ đồ kệ chọn ô (nút bấm) ---- */
div[class*="st-key-sodo_"] div[data-testid="stHorizontalBlock"]{ gap:6px; flex-wrap:nowrap !important; }
div[class*="st-key-sodo_"] div[data-testid="stColumn"]{ min-width:0 !important; flex:1 1 0 !important; width:auto !important; }
div[class*="st-key-sodo_"] div[data-testid="stColumn"]:first-child{ flex:0 0 30px !important; }
div[class*="st-key-sodo_"] div[data-testid="stButton"] > button{
  min-height:62px; padding:6px 2px 14px; border-radius:3px; line-height:1.2;
  background-repeat:no-repeat; background-size:100% 6px; background-position:left bottom; }
div[class*="st-key-sodo_"] div[data-testid="stButton"] > button p{ font-size:.82rem; line-height:1.3; text-align:center; }
.sodo-t{ display:flex; align-items:center; height:62px; font:600 .95rem var(--f-head); color:var(--muted); }

@media (max-width:640px){
  [data-testid="stMainBlockContainer"], .block-container{ padding-top:1.4rem; }
  .strip > div{ padding:12px 12px 14px; } .strip .v{ font-size:1.8rem; }
}
</style>
"""

CSS_TRANG_CHU = """
<style>
.st-key-home_actions button div[data-testid="stMarkdownContainer"]{ width:100%; }
.st-key-home_actions button p{ text-align:left; }
.st-key-home_actions .sec{ margin:8px 0 0; padding:0 0 8px; font-size:1.25rem; }
/* nút thao tác nhanh: lưới 2 cột (luôn 2 cột kể cả điện thoại), icon phía trên - chữ phía dưới */
.st-key-home_actions > div[data-testid="stVerticalBlock"]{ gap:12px; }
.st-key-home_actions > div{ margin:0 !important; }
.st-key-home_actions div[data-testid="stHorizontalBlock"]{ flex-direction:row !important; flex-wrap:nowrap !important; gap:12px; }
.st-key-home_actions div[data-testid="stColumn"]{ min-width:0 !important; flex:1 1 0 !important; width:auto !important; }
.st-key-home_actions div[data-testid="stButton"] > button{
  height:84px; min-height:84px; padding:12px 14px; border-radius:14px; text-align:left; }
/* Streamlit: button > div > div(flex hàng) > [icon, chữ]  ->  đổi div trong cùng thành cột: icon trên, chữ dưới, căn trái */
.st-key-home_actions div[data-testid="stButton"] > button > div{ width:100%; height:100%; display:flex; }
.st-key-home_actions div[data-testid="stButton"] > button > div > div{
  width:100%; height:100%; display:flex !important; flex-direction:column !important;
  align-items:flex-start !important; justify-content:space-between !important; gap:8px; }
.st-key-home_actions div[data-testid="stButton"] > button span[data-testid="stIconMaterial"]{ font-size:1.35rem; }
.st-key-home_actions div[data-testid="stButton"] > button p{ font-size:.98rem; font-weight:700; line-height:1.2; }
.st-key-home_actions .st-key-home_kiem_tra div[data-testid="stButton"] > button,
.st-key-home_actions .st-key-home_lich_su div[data-testid="stButton"] > button{
  background-color:color-mix(in srgb,var(--tc) 14%,var(--paper)); color:var(--tc-dark);
  border-color:color-mix(in srgb,var(--tc) 14%,var(--paper)); }
.st-key-home_actions .st-key-home_kiem_tra div[data-testid="stButton"] > button:hover,
.st-key-home_actions .st-key-home_lich_su div[data-testid="stButton"] > button:hover{
  background-color:color-mix(in srgb,var(--tc) 24%,var(--paper)); color:var(--tc-dark); border-color:var(--tc); }
.st-key-home_actions .st-key-home_tao_ke div[data-testid="stButton"] > button,
.st-key-home_actions .st-key-home_tao_qr div[data-testid="stButton"] > button{
  background-color:color-mix(in srgb,var(--rack) 12%,var(--paper)); color:var(--rack);
  border-color:color-mix(in srgb,var(--rack) 12%,var(--paper)); }
.st-key-home_actions .st-key-home_tao_ke div[data-testid="stButton"] > button:hover,
.st-key-home_actions .st-key-home_tao_qr div[data-testid="stButton"] > button:hover{
  background-color:color-mix(in srgb,var(--rack) 22%,var(--paper)); color:var(--rack); border-color:var(--rack); }
.racks{ display:flex; flex-wrap:wrap; gap:26px 24px; }
.rack{ flex:1 1 320px; min-width:0; }
/* thẻ số liệu */
.kpis{ display:grid; grid-template-columns:repeat(2,1fr); gap:14px; margin:16px 0 18px; }
.kpi{ background:var(--paper); border:1px solid var(--line); border-radius:16px; padding:16px 20px 16px;
  box-shadow:0 1px 2px rgba(18,41,110,.05); min-width:0; }
.kpi .ic{ display:block; width:23px; height:23px; color:var(--rack); margin-bottom:10px; }
.kpi .ic.trong{ color:var(--tc); } .kpi .ic.xuat{ color:var(--beam); }
.kpi .v{ font:600 2.3rem/1.05 var(--f-head); color:var(--ink); font-variant-numeric:tabular-nums; }
.kpi .k{ margin-top:6px; color:var(--muted); font-size:.85rem; font-weight:500; }
@media (max-width:768px){ .kpi{ padding:14px 16px; border-radius:18px; } .kpi .ic{ width:20px; height:20px; margin-bottom:12px; } .kpi .v{ font-size:2rem; } }
.kbar{ height:5px; background:var(--slot); border-radius:3px; margin-top:10px; overflow:hidden; }
.kbar i{ display:block; height:100%; background:var(--rack); border-radius:3px; }
/* lối tắt cho điện thoại: ẩn trên máy tính vì đã có thanh danh mục bên trái */
.st-key-home_actions{ display:none; }
@media (max-width:768px){ .st-key-home_actions{ display:flex !important; flex-direction:column; gap:12px; margin:0 0 16px; } }
/* thẻ sơ đồ kệ: Sơ đồ kho · Kệ N */
div[class*="st-key-sodo_home_"]{ background:var(--paper); border:1px solid var(--line); border-radius:16px;
  padding:16px 20px 14px; margin-bottom:16px; box-shadow:0 1px 2px rgba(18,41,110,.05); }
div[class*="st-key-sodo_home_"] .sodo-t{ height:44px; font:600 .9rem var(--f-ui); }
div[class*="st-key-sodo_home_"] div[data-testid="stButton"] > button{
  min-height:44px; padding:4px 2px 4px; border-radius:10px; background-color:var(--bg); border-color:var(--line); background-size:0 0; }
div[class*="st-key-sodo_home_"] div[data-testid="stButton"] > button p{ font-size:.92rem; font-weight:600; }
.rack-top{ display:flex; justify-content:space-between; align-items:baseline; gap:10px; margin-bottom:10px; }
.rack-top b{ font:600 1.15rem/1.2 var(--f-ui); color:var(--ink); }
.rack-top span{ color:var(--muted); font-size:.95rem; font-variant-numeric:tabular-nums; }
.frame{ background:var(--paper); border-left:7px solid var(--rack); border-right:7px solid var(--rack);
  border-top:4px solid var(--beam); overflow-x:auto; }
.tier{ display:grid; grid-template-columns:30px 1fr; align-items:center; border-bottom:4px solid var(--beam); padding:6px 4px 6px 0; }
.tier .tl{ font:600 .9rem var(--f-head); color:var(--muted); text-align:center; }
.cells{ display:grid; gap:4px; }
.cell{ background:var(--bg); border-radius:2px; padding:5px 5px 6px; min-width:0; }
.cell .cc{ display:block; font-size:.72rem; font-weight:600; color:var(--muted); font-variant-numeric:tabular-nums; white-space:nowrap; }
.cell .ticks{ display:grid; grid-auto-flow:column; grid-auto-columns:1fr; gap:2px; margin-top:4px; }
.cell .ticks i{ display:block; height:7px; background:var(--slot); }
.cell .ticks i.on{ background:var(--rack); }
.cell.full{ background:var(--rack-tint); }
.cell.full .cc{ color:var(--ink); }
.chu-thich{ color:var(--muted); font-size:.9rem; margin:10px 0 0; }
</style>
"""

def _gon_html(html):
    return ''.join((dong.strip() for dong in html.splitlines()))

_EMOJI = re.compile('[🌀-\U0001faff☀-➿⬀-⯿️\u200d]')

def _dep(chuoi):
    s = re.sub('\\s+', ' ', _EMOJI.sub('', chuoi)).strip()
    if s and s.isupper():
        s = re.sub('\\bQr\\b', 'QR', s.capitalize())
    return s

def tieu_de_trang(tieu_de, nho=False, phu=''):
    meta = f'<span class="pg-meta">{_esc(phu)}</span>' if phu else ''
    st.markdown(_gon_html(f"""<div class="pg-head{(' nho' if nho else '')}"><div class="pg-title">{_esc(_dep(tieu_de))}</div>{meta}</div>"""), unsafe_allow_html=True)

def nhan_muc(ten):
    st.markdown(f'<div class="sec">{_esc(ten)}</div>', unsafe_allow_html=True)

# ============ ICON ============

_ICON = {'box': '<path d="M11 21.73a2 2 0 0 0 2 0l7-4A2 2 0 0 0 21 16V8a2 2 0 0 0-1-1.73l-7-4a2 2 0 0 0-2 0l-7 4A2 2 0 0 0 3 8v8a2 2 0 0 0 1 1.73z"/><path d="M12 22V12"/><path d="m3.3 7 8.7 5 8.7-5"/><path d="m7.5 4.27 9 5.15"/>', 'pin': '<path d="M20 10c0 6-8 12-8 12s-8-6-8-12a8 8 0 0 1 16 0Z"/><circle cx="12" cy="10" r="3"/>', 'square': '<rect width="18" height="18" x="3" y="3" rx="2"/>', 'lock': '<rect width="18" height="11" x="3" y="11" rx="2" ry="2"/><path d="M7 11V7a5 5 0 0 1 10 0v4"/>', 'calendar': '<path d="M8 2v4"/><path d="M16 2v4"/><rect width="18" height="18" x="3" y="4" rx="2"/><path d="M3 10h18"/><path d="M8 14h.01"/><path d="M12 14h.01"/><path d="M16 14h.01"/><path d="M8 18h.01"/><path d="M12 18h.01"/><path d="M16 18h.01"/>'}

_ICON['boxcheck'] = '<path d="m16 16 2 2 4-4"/><path d="M21 10V8a2 2 0 0 0-1-1.73l-7-4a2 2 0 0 0-2 0l-7 4A2 2 0 0 0 3 8v8a2 2 0 0 0 1 1.73l7 4a2 2 0 0 0 2 0l2-1.14"/><path d="m7.5 4.27 9 5.15"/><path d="M3.29 7 12 12l8.71-5"/><path d="M12 22V12"/>'

_ICON['nhap'] = '<path d="M16 16h6"/><path d="M19 13v6"/><path d="M21 10V8a2 2 0 0 0-1-1.73l-7-4a2 2 0 0 0-2 0l-7 4A2 2 0 0 0 3 8v8a2 2 0 0 0 1 1.73l7 4a2 2 0 0 0 2 0l2-1.14"/><path d="m7.5 4.27 9 5.15"/><path d="M3.29 7 12 12l8.71-5"/><path d="M12 22V12"/>'

_ICON['xuat'] = '<path d="M16 16h6"/><path d="M21 10V8a2 2 0 0 0-1-1.73l-7-4a2 2 0 0 0-2 0l-7 4A2 2 0 0 0 3 8v8a2 2 0 0 0 1 1.73l7 4a2 2 0 0 0 2 0l2-1.14"/><path d="m7.5 4.27 9 5.15"/><path d="M3.29 7 12 12l8.71-5"/><path d="M12 22V12"/>'

_ICON['boxes'] = '<path d="M2.97 12.92A2 2 0 0 0 2 14.63v3.24a2 2 0 0 0 .97 1.71l3 1.8a2 2 0 0 0 2.06 0L12 19v-5.5l-5-3-4.03 2.42Z"/><path d="m7 16.5-4.74-2.85"/><path d="m7 16.5 5-3"/><path d="M7 16.5v5.17"/><path d="M12 13.5V19l3.97 2.38a2 2 0 0 0 2.06 0l3-1.8a2 2 0 0 0 .97-1.71v-3.24a2 2 0 0 0-.97-1.71L17 10.5l-5 3Z"/><path d="m17 16.5-5-3"/><path d="m17 16.5 4.74-2.85"/><path d="M17 16.5v5.17"/><path d="M7.97 4.42A2 2 0 0 0 7 6.13v4.37l5 3 5-3V6.13a2 2 0 0 0-.97-1.71l-3-1.8a2 2 0 0 0-2.06 0l-3 1.8Z"/><path d="M12 8 7.26 5.15"/><path d="m12 8 4.74-2.85"/><path d="M12 13.5V8"/>'

_ICON['activity'] = '<path d="M22 12h-4l-3 9L9 3l-3 9H2"/>'

_ICON['user'] = '<circle cx="12" cy="8" r="4"/><path d="M4 21a8 8 0 0 1 16 0"/>'

_ICON['bell'] = '<path d="M6 8a6 6 0 0 1 12 0c0 7 3 9 3 9H3s3-2 3-9"/><path d="M10.3 21a1.94 1.94 0 0 0 3.4 0"/>'

def svg_tho(ten, cls=''):
    d = _ICON.get(ten, '')
    c = f' class="{cls}"' if cls else ''
    return f'<svg{c} viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="1.9" stroke-linecap="round" stroke-linejoin="round" aria-hidden="true">{d}</svg>'

def svg_icon(ten, mau='blue'):
    d = _ICON.get(ten)
    if not d:
        return ''
    return f'<svg class="ico c-{mau}" viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="2" stroke-linecap="round" stroke-linejoin="round" aria-hidden="true">{d}</svg>'

def icon_kw(ten):
    try:
        if tuple((int(x) for x in st.__version__.split('.')[:2])) >= (1, 37):
            return {'icon': f':material/{ten}:'}
    except Exception:
        pass
    return {}

ICON_TONG_QUAN = ''

LOGO_TONG_QUAN = ''

def icon_tieu_de():
    if LOGO_TONG_QUAN and os.path.isfile(LOGO_TONG_QUAN):
        try:
            import base64
            mime = {'png': 'image/png', 'jpg': 'image/jpeg', 'jpeg': 'image/jpeg', 'svg': 'image/svg+xml', 'webp': 'image/webp'}.get(LOGO_TONG_QUAN.rsplit('.', 1)[-1].lower(), 'image/png')
            with open(LOGO_TONG_QUAN, 'rb') as f:
                du_lieu = base64.b64encode(f.read()).decode('ascii')
            return f'<img class="ico-img" src="data:{mime};base64,{du_lieu}" alt="">'
        except OSError:
            pass
    return svg_icon(ICON_TONG_QUAN, 'blue')

def html_the_so_lieu(cac_the):
    o = ''.join((f'<div><span class="v">{so}</span><span class="k">{svg_icon(icon, mau)}{nhan}</span><span class="s">{ghi_chu}</span></div>' for icon, so, nhan, ghi_chu, mau in cac_the))
    return _gon_html(f'<div class="strip" style="grid-template-columns:repeat({len(cac_the)},1fr)">{o}</div>')

def thong_ke_kho():
    tong_o = sum((len(hang) for ke in st.session_state.kho.values() for hang in ke))
    tong_vi_tri = sum((len(o) for ke in st.session_state.kho.values() for hang in ke for o in hang))
    da_dung = 0
    o_day = 0
    for ke in st.session_state.kho.values():
        for hang in ke:
            for o in hang:
                so = sum((1 for vt in o if vt is not None))
                da_dung += so
                if so == len(o):
                    o_day += 1
    hom_nay = datetime.now().strftime('%Y-%m-%d')
    nhap_hn = xuat_hn = 0
    for m in doc_lich_su():
        if str(m.get('thoi_gian', '')).startswith(hom_nay):
            if m.get('hanh_dong') == 'Nhập':
                nhap_hn += 1
            elif m.get('hanh_dong') == 'Xuất':
                xuat_hn += 1
    return {'tong_o': tong_o, 'tong_vi_tri': tong_vi_tri, 'da_dung': da_dung, 'con_trong': tong_vi_tri - da_dung, 'ti_le': round(da_dung * 100 / tong_vi_tri) if tong_vi_tri else 0, 'o_day': o_day, 'nhap_hn': nhap_hn, 'xuat_hn': xuat_hn, 'hom_nay': datetime.now().strftime('%d/%m/%Y')}

_THU = ['Thứ hai', 'Thứ ba', 'Thứ tư', 'Thứ năm', 'Thứ sáu', 'Thứ bảy', 'Chủ nhật']

def html_duong_dan(muc):
    return f'<div class="crumb">Trang chủ<i>/</i><b>{_esc(muc)}</b></div>'

def html_dau_trang_chu(tk):
    ngay = f"{_THU[datetime.now().weekday()]}, {tk['hom_nay']}"
    return _gon_html(f"""<div class="hd2"><div>{html_duong_dan('Tổng quan')}<div class="hd2-t">{icon_tieu_de()}Tổng quan kho</div><div class="hd2-s">Theo dõi tình trạng kho hàng</div></div><span class="pg-meta">{ngay}</span></div>""")

def html_the_kpi(tk):
    the = [('boxcheck', f"{tk['da_dung']}/{tk['tong_vi_tri']}", 'Đã sử dụng', ''), ('box trong', tk['con_trong'], 'Còn trống', ''), ('nhap', tk['nhap_hn'], 'Nhập hôm nay', ''), ('xuat', tk['xuat_hn'], 'Xuất hôm nay', '')]
    o = ''.join((f"""<div class="kpi">{svg_tho(ic.split()[0], 'ic ' + ic)}<div class="v">{v}</div><div class="k">{k}</div>{ex}</div>""" for ic, v, k, ex in the))
    canh_bao = ''
    if tk['ti_le'] >= 90:
        canh_bao = f"""<div class="canh-bao">Kho đã dùng {tk['ti_le']}% vị trí. Cần xuất bớt hàng hoặc tạo thêm kệ.</div>"""
    return _gon_html(f'<div class="kpis">{o}</div>{canh_bao}')

def hien_o_trong_kho(ten_ke, h, c):
    o = st.session_state.kho[ten_ke][h][c]
    tieu_de = f'Ô {ma_o(ten_ke, h, c)} — {sum((1 for vt in o if vt is not None))}/{len(o)} vị trí'

    def _noi_dung():
        hien_thi_danh_sach_ma_sp(ten_ke, h, c, co_tieu_de=False)
    if hasattr(st, 'dialog'):
        try:
            st.dialog(tieu_de, width='large')(_noi_dung)()
        except TypeError:
            st.dialog(tieu_de)(_noi_dung)()
    else:
        st.markdown(f'##### {tieu_de}')
        _noi_dung()

def _vao_kiem_tra():
    st.session_state.chuc_nang = 'kiem_tra'
    for k in ('kt_qr_tb', 'kt_qr_o', 'kt_qr_cuoi'):
        st.session_state.pop(k, None)
    st.session_state['kt_cam_n'] = st.session_state.get('kt_cam_n', 0) + 1

def _vao_nhap():
    st.session_state.chuc_nang = 'nhap'
    for k in ('nhap_o', 'nhap_tb', 'nhap_qr_cuoi', 'nhap_hang', 'nhap_cot', 'nhap_ke', 'nhap_tay_tb'):
        st.session_state.pop(k, None)
    st.session_state['nhap_cam_n'] = st.session_state.get('nhap_cam_n', 0) + 1

def _vao_xuat():
    st.session_state.chuc_nang = 'xuat'
    for k in ('xuat_tb', 'xuat_ds', 'xuat_cho_chon', 'xuat_qr_cuoi', 'xuat_hang', 'xuat_cot', 'xuat_ke', 'xuat_tay_tb'):
        st.session_state.pop(k, None)
    st.session_state['xuat_cam_n'] = st.session_state.get('xuat_cam_n', 0) + 1

def _vao_lich_su():
    st.session_state.chuc_nang = 'lich_su'

def _vao_tao_ke():
    st.session_state.chuc_nang = 'tao_ke'
    st.session_state.pop('tao_ke_tb', None)

def _vao_tao_qr():
    st.session_state.chuc_nang = 'tao_qr'
    st.session_state.pop('qr_ket_qua', None)
    st.session_state.pop('qro_ket_qua', None)

def trang_chu():
    st.markdown(_gon_html(CSS_TRANG_CHU), unsafe_allow_html=True)
    tk = thong_ke_kho()
    st.markdown(html_dau_trang_chu(tk), unsafe_allow_html=True)
    st.markdown(html_the_kpi(tk), unsafe_allow_html=True)
    if co_ke():
        o_chon = None
        for ten_ke in sorted(st.session_state.kho, key=lay_so_ke):
            o = ve_so_do_ke(ten_ke, key_prefix='home', kieu='home')
            if o and o_chon is None:
                o_chon = (ten_ke, o[0], o[1])
        if o_chon:
            hien_o_trong_kho(*o_chon)

def khung_tinh_trang_kho(kieu):
    tk = thong_ke_kho()
    if kieu == 'nhap':
        cac_the = [('square', tk['con_trong'], 'Vị trí còn trống', f"trên tổng {tk['tong_vi_tri']} vị trí", 'blue'), ('pin', tk['da_dung'], 'Đang chứa hàng', 'vị trí đã có sản phẩm', 'green'), ('calendar', tk['nhap_hn'], 'Nhập hôm nay', f"lượt, ngày {tk['hom_nay']}", 'violet')]
    elif kieu == 'xuat':
        cac_the = [('pin', tk['da_dung'], 'Đang chứa hàng', 'sản phẩm có thể xuất', 'blue'), ('square', tk['con_trong'], 'Vị trí còn trống', f"trên tổng {tk['tong_vi_tri']} vị trí", 'green'), ('calendar', tk['xuat_hn'], 'Xuất hôm nay', f"lượt, ngày {tk['hom_nay']}", 'violet')]
    else:
        cac_the = [('box', tk['tong_o'], 'Tổng số ô', f'{len(st.session_state.kho)} kệ hàng', 'blue'), ('pin', tk['da_dung'], 'Đang chứa hàng', 'vị trí đã có sản phẩm', 'green'), ('boxes', tk['o_day'], 'Ô đã đầy', 'không còn vị trí trống', 'orange')]
    nhan_muc('Tình trạng kho')
    st.markdown(html_the_so_lieu(cac_the), unsafe_allow_html=True)

def nut_quay_lai():
    st.divider()
    if st.button('Quay lại trang chủ', use_container_width=True, key='quay_lai_trang_chu'):
        st.session_state.chuc_nang = None
        st.rerun()

# ============ VẼ SƠ ĐỒ KỆ HÀNG ============

def ve_so_do_ke(ten_ke, key_prefix='', kieu=''):
    du_lieu_ke = st.session_state.kho[ten_ke]
    o_duoc_chon = None
    so_hang, so_cot = (len(du_lieu_ke), len(du_lieu_ke[0]))
    so_ke = lay_so_ke(ten_ke)
    dau_the = ''
    if kieu == 'home':
        tong_ke = sum((len(o) for hang in du_lieu_ke for o in hang))
        da_ke = sum((1 for hang in du_lieu_ke for o in hang for vt in o if vt is not None))
        dau_the = f'<div class="rack-top"><b>Sơ đồ kho · {_esc(ten_ke)}</b><span>{da_ke}/{tong_ke}</span></div>'
    else:
        st.markdown(f'**{ten_ke}**: {so_hang} hàng × {so_cot} cột')
    css_o = []
    with st.container(key=f'sodo_{key_prefix}_{so_ke}'):
        if dau_the:
            st.markdown(dau_the, unsafe_allow_html=True)
        for h in range(so_hang):
            cols = st.columns([0.3] + [1] * so_cot)
            cols[0].markdown(f'<div class="sodo-t">T{h + 1}</div>', unsafe_allow_html=True)
            for c in range(so_cot):
                vi_tri_list = du_lieu_ke[h][c]
                nhan = ma_o(ten_ke, h, c)
                tong = len(vi_tri_list)
                so_dang_dung = sum((1 for vt in vi_tri_list if vt is not None))
                phan_tram = round(so_dang_dung * 100 / tong) if tong else 0
                khoa = f'{key_prefix}_k{so_ke}_{h}_{c}'
                sel = f'div.st-key-{khoa} div[data-testid="stButton"] > button'
                css_o.append(f'{sel}{{background-image:linear-gradient(90deg,var(--rack) {phan_tram}%,var(--slot) {phan_tram}%);}}')
                if tong and (so_dang_dung == tong or (kieu == 'home' and so_dang_dung > 0)):
                    css_o.append(f'{sel}{{background-color:var(--rack-tint);border-color:var(--rack);}}')
                with cols[c + 1]:
                    if kieu == 'home':
                        bam = st.button(f'{so_dang_dung}/{tong}', key=khoa, use_container_width=True, help=f'Ô {nhan}')
                    else:
                        bam = st.button(f'{nhan}  \n{so_dang_dung}/{tong}', key=khoa, use_container_width=True)
                    if bam:
                        o_duoc_chon = (h, c)
    st.markdown(f"<style>{''.join(css_o)}</style>", unsafe_allow_html=True)
    return o_duoc_chon

def hien_thi_danh_sach_ma_sp(ten_ke, h, c, noi_bat=None, co_tieu_de=True):
    vi_tri_list = st.session_state.kho[ten_ke][h][c]
    if co_tieu_de:
        st.markdown(f'##### Danh sách sản phẩm trong ô **{ma_o(ten_ke, h, c)}**')
    bang_ten, bang_loai = (doc_ten_day_du(), doc_ten_loai_day_du())
    for idx in range(len(vi_tri_list)):
        vt = vi_tri_list[idx]
        col_nhan, col_noi_dung = st.columns([1, 3])
        with col_nhan:
            st.write(f"**{('' if idx == noi_bat else '')}Vị trí {idx + 1}:**")
        with col_noi_dung:
            if vt is None:
                st.write('_(Trống - chưa có sản phẩm)_')
            else:
                ma = ma_san_pham(ten_ke, h, c, vt['ten_hang'], vt['loai'], vt['stt'])
                dong = f"`{ma}` — Tên: **{ten_day_du(vt['ten_hang'], bang_ten)}** — Loại: **{ten_loai_day_du(vt['ten_hang'], vt['loai'], bang_loai)}**"
                st.write(f'{dong}' if idx == noi_bat else dong)

# ============ CHỨC NĂNG: KIỂM TRA ============

# ============ KIỂM TRA: QUÉT QR VỊ TRÍ Ô ĐỂ XEM SẢN PHẨM TRONG Ô ============

def xu_ly_quet_kiem_tra(noi_dung):
    noi_dung = (noi_dung or '').strip()
    if not noi_dung:
        return
    o = phan_tich_ma_o(noi_dung)
    if o is None:
        st.session_state['kt_qr_tb'] = ('error', f'`{noi_dung}` không phải mã vị trí ô hợp lệ (VD: K1T101). Hãy quét QR **vị trí ô** để xem sản phẩm trong ô.')
        return
    ten_ke, h, c = o
    so_dung = sum((1 for vt in st.session_state.kho[ten_ke][h][c] if vt is not None))
    tong_vt = len(st.session_state.kho[ten_ke][h][c])
    st.session_state['kt_qr_o'] = o
    if so_dung == 0:
        st.session_state['kt_qr_tb'] = ('info', f'Ô **{ma_o(ten_ke, h, c)}** ({ten_ke}, tầng {h + 1}, ô số {c + 1})đang **trống** (0/{tong_vt} vị trí).')
    else:
        st.session_state['kt_qr_tb'] = ('success', f'Ô **{ma_o(ten_ke, h, c)}** ({ten_ke}, tầng {h + 1}, ô số {c + 1})đang có **{so_dung}/{tong_vt}** sản phẩm, còn {tong_vt - so_dung} vị trí trống.')

def _hien_thi_ket_qua_kiem_tra():
    tb = st.session_state.get('kt_qr_tb')
    if not tb:
        return
    getattr(st, tb[0])(tb[1])
    o = st.session_state.get('kt_qr_o')
    if o is not None:
        st.divider()
        hien_thi_danh_sach_ma_sp(*o)

def kiem_tra_bang_quet_qr():
    _nut_mo_camera('kt', 'quet_kiem_tra', key='kt_mo_cam')
    khung_tinh_trang_kho('kiem_tra')
    if st.session_state.get('kt_qr_tb'):
        nhan_muc('Kết quả lần quét gần nhất')
    _hien_thi_ket_qua_kiem_tra()

def man_hinh_quet_kiem_tra():
    if st.button('Quay lại trang kiểm tra', key='kt_quay_lai'):
        st.session_state.chuc_nang = 'kiem_tra'
        st.rerun()
    tieu_de_trang('Quét QR kiểm tra ô', nho=True)
    if _camera_quet('kt', 'kt_scan', xu_ly_quet_kiem_tra) is None:
        return
    st.subheader('Quét QR vị trí ô cần xem')
    _hien_thi_ket_qua_kiem_tra()
    st.divider()
    if st.button('Xong', use_container_width=True, key='kt_xong'):
        st.session_state.chuc_nang = 'kiem_tra'
        st.rerun()

def man_hinh_kiem_tra():
    tieu_de_trang('Kiểm tra kho hàng')
    kiem_tra_bang_quet_qr()
    nut_quay_lai()

# ============ PHÂN TÍCH NỘI DUNG QR ============

def moi_o(cac_ke=None):
    for ten_ke in st.session_state.kho if cac_ke is None else cac_ke:
        ke = st.session_state.kho[ten_ke]
        for h in range(len(ke)):
            for c in range(len(ke[0])):
                yield (ten_ke, h, c, ke[h][c])

def phan_tich_ma_o(noi_dung):
    ma = noi_dung.strip().upper()
    return next(((k, h, c) for k, h, c, _ in moi_o() if ma_o(k, h, c) == ma), None)

def phan_tich_ma_sp(noi_dung):
    ma = noi_dung.strip()
    m = re.fullmatch('[Kk](\\d+)-(.+)-([^-]+)-(\\d+)', ma)
    if m and m.group(2).strip() and m.group(3).strip() and (int(m.group(4)) >= 1):
        return (m.group(2).strip(), m.group(3).strip(), int(m.group(4)), int(m.group(1)))
    phan = [p.strip() for p in ma.rsplit('-', 2)]
    if len(phan) != 3 or not all(phan) or (not phan[2].isdigit()) or (int(phan[2]) < 1):
        return None
    return (phan[0], phan[1], int(phan[2]), None)

def _nut_mo_camera(tien_to, trang_quet, key=None):
    if st.button('Mở camera quét QR', type='primary', use_container_width=True, key=key):
        st.session_state.pop(f'{tien_to}_qr_cuoi', None)
        st.session_state[f'{tien_to}_cam_n'] = st.session_state.get(f'{tien_to}_cam_n', 0) + 1
        st.session_state.chuc_nang = trang_quet
        st.rerun()

def _camera_quet(tien_to, khoa, xu_ly):
    if _QR_LIVE is None:
        st.error('Không tạo được thành phần camera (không ghi được file vào thư mục chạy app). Hãy kiểm tra quyền ghi thư mục.')
        return None
    n = st.session_state.get(f'{tien_to}_cam_n', 0)
    ket_qua = _QR_LIVE(key=f'{khoa}_{n}', default=None)
    if ket_qua and ket_qua.get('id') != st.session_state.get(f'{tien_to}_qr_cuoi'):
        st.session_state[f'{tien_to}_qr_cuoi'] = ket_qua['id']
        xu_ly(str(ket_qua.get('code', '')))
    return n

def hien_thong_bao_nhap(tb):
    loai, noi_dung = tb
    if loai == 'sai_ke':
        html_nd = re.sub('\\*\\*(.+?)\\*\\*', '<b>\\1</b>', str(noi_dung).replace('<', '&lt;').replace('>', '&gt;'))
        html_nd = re.sub('`(.+?)`', "<code style='color:#fff;background:#a31515;padding:1px 6px;border-radius:4px;'>\\1</code>", html_nd)
        st.markdown(f"<div style='background:#d32f2f;color:#fff;border:3px solid #7f0000;border-radius:10px;padding:16px 20px;margin:8px 0;font-size:1.05rem;line-height:1.5;'><div style='font-size:1.4rem;font-weight:800;margin-bottom:4px;'>⛔ SẢN PHẨM NHẬP SAI KỆ!</div>{html_nd}</div>", unsafe_allow_html=True)
        return
    getattr(st, loai)(noi_dung)

def xu_ly_quet_nhap(noi_dung):
    noi_dung = (noi_dung or '').strip()
    if not noi_dung:
        return
    o = phan_tich_ma_o(noi_dung)
    if o:
        st.session_state['nhap_o'] = o
        st.session_state['nhap_tb'] = ('success', f'Đã chọn ô **{ma_o(*o)}** ({o[0]}). Bây giờ hãy quét QR sản phẩm.')
        return
    if 'nhap_o' not in st.session_state:
        sp_truoc = phan_tich_ma_sp(noi_dung)
        goi_y = f' Mã này thuộc **Kệ {sp_truoc[3]}**, hãy quét QR ô của Kệ {sp_truoc[3]}.' if sp_truoc and sp_truoc[3] else ''
        st.session_state['nhap_tb'] = ('error', f'Chưa chọn ô. Hãy quét QR vị trí ô trước (đã quét: `{noi_dung}`).{goi_y}')
        return
    sp = phan_tich_ma_sp(noi_dung)
    if sp is None:
        st.session_state['nhap_tb'] = ('error', f'QR `{noi_dung}` không đúng định dạng **Kệ-Tên-Loại-STT** (VD: K1-RLY-ABC-001) và cũng không phải mã ô.')
        return
    ten_hang, loai, stt, so_ke_qr = sp
    ten_ke_chon = st.session_state['nhap_o'][0]
    if so_ke_qr is None:
        st.session_state['nhap_tb'] = ('error', f'QR `{noi_dung}` chưa có số kệ nên không biết thuộc kệ nào. Hãy tạo lại tem theo dạng **K{{kệ}}-Tên-Loại-STT** (VD: K1-RLY-ABC-001).')
        return
    if so_ke_qr != lay_so_ke(ten_ke_chon):
        st.session_state['nhap_tb'] = ('sai_ke', f'Sản phẩm `{noi_dung}` thuộc **Kệ {so_ke_qr}** nhưng ô đang chọn nằm ở **{ten_ke_chon}**. Hãy quét QR ô của Kệ {so_ke_qr}.')
        return
    da_co = tim_san_pham_trong_kho(ten_hang, loai, stt)
    if da_co:
        cac_cho = ', '.join((f'ô **{ma_o(k, hh, cc)}** (Vị trí {i + 1})' for k, hh, cc, i in da_co))
        st.session_state['nhap_tb'] = ('warning', f'Sản phẩm `{noi_dung}` **đã có trong kho** tại {cac_cho}, không nhập lại. Nếu muốn chuyển sang ô khác, hãy xuất sản phẩm ra trước.')
        return
    ten_ke, h, c = st.session_state['nhap_o']
    vi_tri_list = st.session_state.kho[ten_ke][h][c]
    vi_tri_trong = [i for i in range(len(vi_tri_list)) if vi_tri_list[i] is None]
    if not vi_tri_trong:
        st.session_state['nhap_tb'] = ('error', f'Ô **{ma_o(ten_ke, h, c)}** đã đầy {len(vi_tri_list)}/{len(vi_tri_list)} vị trí. Hãy quét QR của ô khác.')
        return
    idx = vi_tri_trong[0]
    vi_tri_list[idx] = {'ten_hang': ten_hang, 'loai': loai, 'stt': stt}
    ma_moi = ma_san_pham(ten_ke, h, c, ten_hang, loai, stt)
    luu_du_lieu(st.session_state.kho)
    ghi_lich_su('Nhập', ma_moi, ten_hang, loai)
    st.session_state['nhap_tb'] = ('success', f'Đã nhập `{ma_moi}` vào **Vị trí {idx + 1}** của ô {ma_o(ten_ke, h, c)}.Có thể quét tiếp sản phẩm khác.')

# ============ CAMERA QUÉT QR TRỰC TIẾP (tự xây, không cần cài thêm thư viện) ============

QR_LIVE_HTML = r'''<!DOCTYPE html>
<html lang="vi">
<head>
<meta charset="utf-8">
<meta name="viewport" content="width=device-width, initial-scale=1">
<style>
  html, body { margin: 0; padding: 0; background: transparent; overflow: hidden;
               font-family: -apple-system, "Segoe UI", Roboto, sans-serif; }
  #box { position: relative; width: 100%; max-width: 420px; aspect-ratio: 1 / 1; margin: 0 auto;
         box-sizing: border-box; border: 3px solid #ffffff; border-radius: 16px;
         overflow: hidden; background: #000; transition: border-color .15s; }
  #box.ok { border-color: #21c55e; }
  video { position: absolute; inset: 0; width: 100%; height: 100%; object-fit: cover; }
  #khung { position: absolute; top: 50%; left: 50%; width: 66%; aspect-ratio: 1 / 1;
           transform: translate(-50%, -50%); border-radius: 12px;
           box-shadow: 0 0 0 9999px rgba(0, 0, 0, .45); }
  .c { position: absolute; width: 28px; height: 28px; border: 4px solid #ffffff; transition: border-color .15s; }
  #box.ok .c { border-color: #21c55e; }
  .tl { top: 0; left: 0; border-right: 0; border-bottom: 0; border-top-left-radius: 12px; }
  .tr { top: 0; right: 0; border-left: 0; border-bottom: 0; border-top-right-radius: 12px; }
  .bl { bottom: 0; left: 0; border-right: 0; border-top: 0; border-bottom-left-radius: 12px; }
  .br { bottom: 0; right: 0; border-left: 0; border-top: 0; border-bottom-right-radius: 12px; }
  #line { position: absolute; left: 6%; right: 6%; height: 2px; background: #ffffff;
          box-shadow: 0 0 8px #ffffff; animation: quet 2.2s ease-in-out infinite alternate; }
  #box.ok #line { background: #21c55e; box-shadow: 0 0 8px #21c55e; }
  @keyframes quet { from { top: 8%; } to { top: 92%; } }
  #msg { position: absolute; left: 0; right: 0; bottom: 0; padding: 8px 10px; box-sizing: border-box;
         color: #fff; background: rgba(0, 0, 0, .65); font-size: 14px; text-align: center; }
  #msg.err { background: rgba(185, 28, 28, .9); }
</style>
</head>
<body>
<div id="box">
  <video id="video" playsinline muted autoplay></video>
  <div id="khung">
    <span class="c tl"></span><span class="c tr"></span><span class="c bl"></span><span class="c br"></span>
    <div id="line"></div>
  </div>
  <div id="msg">Đang mở camera...</div>
</div>
<script>
(function () {
  var COOLDOWN = 2500;           // ms: cùng 1 mã còn trong khung hình thì không gửi lại
  var JSQR_URL = "https://cdn.jsdelivr.net/npm/jsqr@1.4.0/dist/jsQR.js";

  var box = document.getElementById("box");
  var video = document.getElementById("video");
  var msg = document.getElementById("msg");
  var canvas = document.createElement("canvas");
  var ctx = canvas.getContext("2d", { willReadFrequently: true });
  var detector = null, lastCode = null, lastSeen = 0, busy = false, stream = null, msgTimer = null;

  function send(type, extra) {
    window.parent.postMessage(Object.assign({ isStreamlitMessage: true, type: "streamlit:" + type }, extra), "*");
  }
  function setHeight() { send("setFrameHeight", { height: Math.ceil(box.getBoundingClientRect().height) + 2 }); }
  function setMsg(text, isErr) { msg.textContent = text; msg.className = isErr ? "err" : ""; }

  window.addEventListener("message", function (e) {
    if (e.data && e.data.type === "streamlit:render") setHeight();
  });
  if (window.ResizeObserver) new ResizeObserver(setHeight).observe(box);
  send("componentReady", { apiVersion: 1 });
  setHeight();

  function loadJsQR() {
    return new Promise(function (resolve, reject) {
      if (window.jsQR) return resolve();
      var s = document.createElement("script");
      s.src = JSQR_URL; s.onload = resolve; s.onerror = reject;
      document.head.appendChild(s);
    });
  }
  function needJsQR() {
    loadJsQR().catch(function () { setMsg("Không tải được bộ giải mã QR. Kiểm tra kết nối mạng.", true); });
  }

  if ("BarcodeDetector" in window) {
    try { detector = new window.BarcodeDetector({ formats: ["qr_code"] }); } catch (e) { detector = null; }
  }
  if (!detector) needJsQR();

  // Cắt đúng vùng vuông ở giữa khung hình (giống phần người dùng nhìn thấy) rồi giải mã
  async function decode() {
    var vw = video.videoWidth, vh = video.videoHeight;
    if (!vw || !vh) return null;
    var side = Math.min(vw, vh), out = Math.min(side, 720);
    canvas.width = out; canvas.height = out;
    ctx.drawImage(video, (vw - side) / 2, (vh - side) / 2, side, side, 0, 0, out, out);
    if (detector) {
      try {
        var r = await detector.detect(canvas);
        return (r && r.length) ? r[0].rawValue : null;
      } catch (e) { detector = null; needJsQR(); return null; }
    }
    if (window.jsQR) {
      var img = ctx.getImageData(0, 0, out, out);
      var res = window.jsQR(img.data, out, out, { inversionAttempts: "dontInvert" });
      if (res) {
        try {
          if (res.binaryData && res.binaryData.length)
            return new TextDecoder("utf-8").decode(new Uint8Array(res.binaryData));
        } catch (e) {}
        return res.data;
      }
    }
    return null;
  }

  function handle(code) {
    if (!code) return;
    code = code.trim();
    if (!code) return;
    var now = Date.now();
    if (code === lastCode && now - lastSeen < COOLDOWN) { lastSeen = now; return; }
    lastCode = code; lastSeen = now;
    box.classList.add("ok");
    setMsg("Đã quét: " + code, false);
    if (navigator.vibrate) { try { navigator.vibrate(80); } catch (e) {} }
    clearTimeout(msgTimer);
    msgTimer = setTimeout(function () { box.classList.remove("ok"); setMsg("Đưa mã QR vào khung vuông", false); }, 1500);
    send("setComponentValue", {
      value: { code: code, id: now + "-" + Math.random().toString(36).slice(2, 8) },
      dataType: "json"
    });
  }

  async function tick() {
    if (!busy && video.readyState >= 2) {
      busy = true;
      try { handle(await decode()); } catch (e) {}
      busy = false;
    }
    setTimeout(tick, 120);
  }

  async function startCam() {
    try {
      stream = await navigator.mediaDevices.getUserMedia({
        video: { facingMode: { ideal: "environment" }, width: { ideal: 1280 }, height: { ideal: 720 } },
        audio: false
      });
      video.srcObject = stream;
      await video.play();
      setMsg("Đưa mã QR vào khung vuông", false);
      tick();
    } catch (e) {
      setMsg("Không mở được camera (" + (e.name || e.message) + "). Hãy cho phép quyền camera và dùng HTTPS.", true);
    }
  }
  window.addEventListener("pagehide", function () {
    if (stream) stream.getTracks().forEach(function (t) { t.stop(); });
  });
  startCam();
})();
</script>
</body>
</html>
'''

def _tao_component_qr():
    for thu_muc in (Path(__file__).resolve().parent / 'qr_live_component', Path(tempfile.gettempdir()) / 'qr_live_component'):
        try:
            thu_muc.mkdir(exist_ok=True)
            f = thu_muc / 'index.html'
            if not f.exists() or f.read_text(encoding='utf-8') != QR_LIVE_HTML:
                f.write_text(QR_LIVE_HTML, encoding='utf-8')
            return components.declare_component('qr_live_scanner', path=str(thu_muc))
        except OSError:
            continue
    return None

_QR_LIVE = _tao_component_qr()

# ============ CHỨC NĂNG: NHẬP HÀNG (QUÉT QR) ============

def nhap_bang_quet_qr():
    _nut_mo_camera('nhap', 'quet_nhap')
    khung_tinh_trang_kho('nhap')
    tb = st.session_state.get('nhap_tb')
    if tb and tb[0] == 'sai_ke':
        hien_thong_bao_nhap(tb)
    o_chon = st.session_state.get('nhap_o')
    if o_chon is not None:
        ten_ke, h, c = o_chon
        hien_thi_danh_sach_ma_sp(ten_ke, h, c)
        if st.button('Bỏ chọn ô này'):
            st.session_state.pop('nhap_o', None)
            st.rerun()

def man_hinh_nhap():
    tieu_de_trang('Nhập hàng vào kho')
    tab_quet, tab_tay = st.tabs(['Quét QR', 'Nhập tay'])
    with tab_quet:
        nhap_bang_quet_qr()
    with tab_tay:
        nhap_tay()
    nut_quay_lai()

def nhap_tay():
    tb = st.session_state.pop('nhap_tay_tb', None)
    if tb:
        st.success(tb)
    nhan_muc('Chọn ô cần nhập')
    ten_ke = st.selectbox('Chọn kệ', list(st.session_state.kho), key='nhap_tay_ke')
    o_chon = ve_so_do_ke(ten_ke, key_prefix='nhap')
    if o_chon:
        st.session_state['nhap_ke'] = ten_ke
        st.session_state['nhap_hang'] = o_chon[0]
        st.session_state['nhap_cot'] = o_chon[1]
    if 'nhap_hang' in st.session_state and st.session_state.get('nhap_ke') == ten_ke:
        h, c = (st.session_state['nhap_hang'], st.session_state['nhap_cot'])
        st.divider()
        hien_thi_danh_sach_ma_sp(ten_ke, h, c)
        vi_tri_list = st.session_state.kho[ten_ke][h][c]
        vi_tri_trong = [i for i in range(len(vi_tri_list)) if vi_tri_list[i] is None]
        ten_hien_co = sorted({vt['ten_hang'] for vt in vi_tri_list if vt is not None})
        st.divider()
        st.subheader('Nhập sản phẩm')
        if not vi_tri_trong:
            st.error(f'Ô này đã đầy {len(vi_tri_list)}/{len(vi_tri_list)} vị trí, không thể nhập thêm. Vui lòng chọn ô khác hoặc xuất bớt.')
        else:
            tuy_chon_ten = ten_hien_co + ['+ Thêm mã sản phẩm mới']
            lua_chon_ten = st.selectbox('Chọn mã sản phẩm', tuy_chon_ten, key='chon_ten_nhap')
            with st.form('form_nhap'):
                if lua_chon_ten == '+ Thêm mã sản phẩm mới':
                    ten_hang = st.text_input('Mã sản phẩm mới (đúng 3 ký tự)', max_chars=3, placeholder='VD: RLY')
                else:
                    ten_hang = lua_chon_ten
                    st.text_input('Mã sản phẩm', value=ten_hang, disabled=True)
                loai = st.text_input('Mã loại sản phẩm (đúng 3 ký tự)', max_chars=3, placeholder='VD: ABC')
                so_luong_tao = st.number_input(f'Số sản phẩm cần nhập (mỗi sản phẩm chiếm 1 vị trí, tối đa {len(vi_tri_trong)})', min_value=1, max_value=len(vi_tri_trong), value=1, step=1)
                submit = st.form_submit_button('Xác nhận nhập hàng', type='primary')
                if submit:
                    la_moi = lua_chon_ten == '+ Thêm mã sản phẩm mới'
                    if not ten_hang or not ten_hang.strip():
                        st.error('Vui lòng nhập mã sản phẩm.')
                    elif la_moi and (not ma_hop_le(ten_hang)):
                        st.error('Mã sản phẩm phải đúng 3 ký tự chữ hoặc số, không dấu (VD: RLY).')
                    elif not ma_hop_le(loai):
                        st.error('Mã loại sản phẩm phải đúng 3 ký tự chữ hoặc số, không dấu (VD: ABC).')
                    elif stt_lon_nhat_trong_kho(ten_hang, loai) + int(so_luong_tao) > STT_MAX:
                        st.error(f'STT chỉ có 3 chữ số (tối đa {STT_MAX}). Sản phẩm này đã có STT đến {stt_lon_nhat_trong_kho(ten_hang, loai)}, không nhập thêm {int(so_luong_tao)} được.')
                    else:
                        ten_hang = chuan_hoa(ten_hang) if la_moi else ten_hang.strip()
                        loai = chuan_hoa(loai)
                        stt_hien_tai = stt_lon_nhat_trong_kho(ten_hang, loai)
                        ma_moi = []
                        for i in range(int(so_luong_tao)):
                            idx_vi_tri = vi_tri_trong[i]
                            stt = stt_hien_tai + i + 1
                            vi_tri_list[idx_vi_tri] = {'ten_hang': ten_hang, 'loai': loai, 'stt': stt}
                            ma_moi.append(ma_san_pham(ten_ke, h, c, ten_hang, loai, stt))
                        luu_du_lieu(st.session_state.kho)
                        for ma_sp in ma_moi:
                            ghi_lich_su('Nhập', ma_sp, ten_hang, loai)
                        st.session_state['nhap_tay_tb'] = f"Đã nhập {len(ma_moi)} '{ten_hang}' (loại: {loai}) vào ô {ma_o(ten_ke, h, c)}. Mã: " + ', '.join((f'`{m}`' for m in ma_moi))
                        for k in ('nhap_hang', 'nhap_cot', 'nhap_ke'):
                            st.session_state.pop(k, None)
                        st.rerun()

def man_hinh_quet_nhap():
    if st.button('Quay lại trang nhập hàng'):
        st.session_state.chuc_nang = 'nhap'
        st.rerun()
    tieu_de_trang('Quét QR nhập hàng', nho=True)
    n = _camera_quet('nhap', 'nhap_qr', xu_ly_quet_nhap)
    if n is None:
        return
    o_chon = st.session_state.get('nhap_o')
    if o_chon is None:
        st.subheader('Bước 1: Quét QR vị trí ô')
    else:
        ten_ke, h, c = o_chon
        st.subheader('Bước 2: Quét QR sản phẩm')
    tb = st.session_state.get('nhap_tb')
    if tb:
        hien_thong_bao_nhap(tb)
    col_a, col_b = st.columns(2)
    with col_a:
        if o_chon is not None and st.button('Chọn ô khác', use_container_width=True):
            st.session_state.pop('nhap_o', None)
            st.session_state.pop('nhap_qr_cuoi', None)
            st.session_state['nhap_cam_n'] = n + 1
            st.rerun()
    with col_b:
        if st.button('Xong, xem kết quả', use_container_width=True):
            st.session_state.chuc_nang = 'nhap'
            st.rerun()

# ============ CHỨC NĂNG: XUẤT HÀNG (QUÉT QR SẢN PHẨM) ============

def tim_san_pham_trong_kho(ten_hang, loai, stt):
    ten_c, loai_c = (chuan_hoa(ten_hang), chuan_hoa(loai))
    return [(ten_ke, h, c, i) for ten_ke, h, c, o in moi_o() for i, vt in enumerate(o) if vt is not None and chuan_hoa(vt['ten_hang']) == ten_c and (chuan_hoa(vt['loai']) == loai_c) and (vt['stt'] == stt)]

def stt_lon_nhat_trong_kho(ten_hang, loai):
    ten_c, loai_c = (chuan_hoa(ten_hang), chuan_hoa(loai))
    return max((vt['stt'] for _, _, _, o in moi_o() for vt in o if vt is not None and chuan_hoa(vt['ten_hang']) == ten_c and (chuan_hoa(vt['loai']) == loai_c)), default=0)

def thuc_hien_xuat(ten_ke, h, c, idx):
    vi_tri_list = st.session_state.kho[ten_ke][h][c]
    vt = vi_tri_list[idx]
    ma = ma_san_pham(ten_ke, h, c, vt['ten_hang'], vt['loai'], vt['stt'])
    vi_tri_list[idx] = None
    luu_du_lieu(st.session_state.kho)
    ghi_lich_su('Xuất', ma, vt['ten_hang'], vt['loai'])
    st.session_state.setdefault('xuat_ds', []).append({'thoi_gian': datetime.now().strftime('%H:%M:%S'), 'ma': ma, 'ten_hang': vt['ten_hang'], 'loai': vt['loai'], 'vi_tri': f'Ô {ma_o(ten_ke, h, c)} - Vị trí {idx + 1}'})
    st.session_state['xuat_tb'] = ('success', f"Đã xuất `{ma}` ({ten_day_du(vt['ten_hang'])} / {ten_loai_day_du(vt['ten_hang'], vt['loai'])}) từ ô **{ma_o(ten_ke, h, c)}** — Vị trí {idx + 1}.")

def xu_ly_quet_xuat(noi_dung):
    noi_dung = (noi_dung or '').strip()
    if not noi_dung:
        return
    st.session_state.pop('xuat_cho_chon', None)
    if phan_tich_ma_o(noi_dung):
        st.session_state['xuat_tb'] = ('error', f'`{noi_dung}` là mã của ô. Xuất hàng chỉ cần quét QR **sản phẩm** (dạng Kệ-Tên-Loại-STT).')
        return
    sp = phan_tich_ma_sp(noi_dung)
    if sp is None:
        st.session_state['xuat_tb'] = ('error', f'QR `{noi_dung}` không đúng định dạng **Kệ-Tên-Loại-STT** (VD: K1-RLY-ABC-001).')
        return
    ten_hang, loai, stt, _so_ke = sp
    vi_tri_tim_thay = tim_san_pham_trong_kho(ten_hang, loai, stt)
    if not vi_tri_tim_thay:
        st.session_state['xuat_tb'] = ('warning', f'Không tìm thấy sản phẩm `{noi_dung}` trong kho (có thể đã được xuất rồi).')
    elif len(vi_tri_tim_thay) == 1:
        thuc_hien_xuat(*vi_tri_tim_thay[0])
    else:
        st.session_state['xuat_cho_chon'] = {'ma': noi_dung, 'vi_tri': vi_tri_tim_thay}
        st.session_state['xuat_tb'] = ('warning', f'Sản phẩm `{noi_dung}` có ở **{len(vi_tri_tim_thay)} vị trí** khác nhau. Hãy chọn xuất từ vị trí nào bên dưới.')

def _hien_thi_ds_da_xuat():
    ds = st.session_state.get('xuat_ds', [])
    if not ds:
        return
    st.markdown(f'##### Đã xuất trong phiên này: **{len(ds)}** sản phẩm')
    bang_ten, bang_loai = (doc_ten_day_du(), doc_ten_loai_day_du())
    for m in reversed(ds):
        st.write(f"`{m['thoi_gian']}` — `{m['ma']}` — {ten_day_du(m['ten_hang'], bang_ten)} / {ten_loai_day_du(m['ten_hang'], m['loai'], bang_loai)} — {m['vi_tri']}")

def xuat_bang_quet_qr():
    _nut_mo_camera('xuat', 'quet_xuat')
    khung_tinh_trang_kho('xuat')
    tb = st.session_state.get('xuat_tb')
    if tb:
        nhan_muc('Kết quả lần quét gần nhất')
        getattr(st, tb[0])(tb[1])
    _hien_thi_ds_da_xuat()

def man_hinh_xuat():
    tieu_de_trang('Xuất hàng khỏi kho')
    tab_quet, tab_tay = st.tabs(['Quét QR', 'Xuất tay'])
    with tab_quet:
        xuat_bang_quet_qr()
    with tab_tay:
        xuat_tay()
    nut_quay_lai()

def xuat_tay():
    tb = st.session_state.pop('xuat_tay_tb', None)
    if tb:
        st.success(tb)
    nhan_muc('Chọn ô cần xuất')
    ten_ke = st.selectbox('Chọn kệ', list(st.session_state.kho), key='xuat_tay_ke')
    o_chon = ve_so_do_ke(ten_ke, key_prefix='xuat')
    if o_chon:
        h, c = o_chon
        if all((vt is None for vt in st.session_state.kho[ten_ke][h][c])):
            st.warning('Ô bạn vừa chọn đang trống, không có hàng để xuất.')
        else:
            st.session_state['xuat_ke'] = ten_ke
            st.session_state['xuat_hang'] = h
            st.session_state['xuat_cot'] = c
    if 'xuat_hang' in st.session_state and st.session_state.get('xuat_ke') == ten_ke:
        h, c = (st.session_state['xuat_hang'], st.session_state['xuat_cot'])
        vi_tri_list = st.session_state.kho[ten_ke][h][c]
        st.divider()
        hien_thi_danh_sach_ma_sp(ten_ke, h, c)
        vi_tri_co_hang = [i for i in range(len(vi_tri_list)) if vi_tri_list[i] is not None]
        if vi_tri_co_hang:
            st.divider()
            bang_ten, bang_loai = (doc_ten_day_du(), doc_ten_loai_day_du())
            tuy_chon = [f"Vị trí {i + 1}: {ma_san_pham(ten_ke, h, c, vi_tri_list[i]['ten_hang'], vi_tri_list[i]['loai'], vi_tri_list[i]['stt'])} — {ten_day_du(vi_tri_list[i]['ten_hang'], bang_ten)} / {ten_loai_day_du(vi_tri_list[i]['ten_hang'], vi_tri_list[i]['loai'], bang_loai)}" for i in vi_tri_co_hang]
            lua_chon = st.multiselect('Chọn (một hoặc nhiều) mã sản phẩm cần xuất', tuy_chon, key='xuat_tay_chon')
            if lua_chon and st.button('Xác nhận xuất hàng', type='primary', key='xuat_tay_ok'):
                idx_can_xuat = [vi_tri_co_hang[tuy_chon.index(lc)] for lc in lua_chon]
                da_xuat = []
                for idx in idx_can_xuat:
                    vt = vi_tri_list[idx]
                    ma = ma_san_pham(ten_ke, h, c, vt['ten_hang'], vt['loai'], vt['stt'])
                    ghi_lich_su('Xuất', ma, vt['ten_hang'], vt['loai'])
                    da_xuat.append(ma)
                    vi_tri_list[idx] = None
                luu_du_lieu(st.session_state.kho)
                st.session_state['xuat_tay_tb'] = f'Đã xuất {len(da_xuat)} sản phẩm: ' + ', '.join((f'`{m}`' for m in da_xuat))
                st.session_state.pop('xuat_tay_chon', None)
                st.rerun()

def man_hinh_quet_xuat():
    if st.button('Quay lại trang xuất hàng'):
        st.session_state.chuc_nang = 'xuat'
        st.rerun()
    tieu_de_trang('Quét QR xuất hàng', nho=True)
    if _camera_quet('xuat', 'xuat_qr', xu_ly_quet_xuat) is None:
        return
    st.subheader('Quét QR sản phẩm cần xuất')
    tb = st.session_state.get('xuat_tb')
    if tb:
        getattr(st, tb[0])(tb[1])
    cho = st.session_state.get('xuat_cho_chon')
    if cho:
        for k, (ten_ke, h, c, i) in enumerate(cho['vi_tri']):
            if st.button(f'Xuất từ ô {ma_o(ten_ke, h, c)} — Vị trí {i + 1}', key=f'xuat_chon_{k}', use_container_width=True):
                thuc_hien_xuat(ten_ke, h, c, i)
                st.session_state.pop('xuat_cho_chon', None)
                st.rerun()
    st.divider()
    _hien_thi_ds_da_xuat()
    if st.button('Xong, xem kết quả', use_container_width=True):
        st.session_state.chuc_nang = 'xuat'
        st.rerun()

# ============ CHỨC NĂNG: LỊCH SỬ NHẬP / XUẤT ============

def man_hinh_lich_su():
    tieu_de_trang('Lịch sử nhập / xuất')
    du_lieu = doc_lich_su()
    if not du_lieu:
        nut_quay_lai()
        return
    df = pd.DataFrame(du_lieu).rename(columns={'thoi_gian': 'Thời gian', 'hanh_dong': 'Hành động', 'ma_san_pham': 'Mã sản phẩm', 'ten_hang': 'Tên hàng', 'loai': 'Loại'})
    bang_ten, bang_loai = (doc_ten_day_du(), doc_ten_loai_day_du())
    df['Loại'] = [ten_loai_day_du(t, l, bang_loai) if isinstance(t, str) and isinstance(l, str) else l for t, l in zip(df['Tên hàng'], df['Loại'])]
    df['Tên hàng'] = df['Tên hàng'].map(lambda t: ten_day_du(t, bang_ten) if isinstance(t, str) else t)
    df['Thời gian'] = pd.to_datetime(df['Thời gian'], errors='coerce')
    df['Mã ô'] = df['Mã sản phẩm'].str.split('-').str[0]
    df = df.sort_values('Thời gian', ascending=False).reset_index(drop=True)
    nhan_muc('Bộ lọc')
    c1, c2, c3, c4 = st.columns([1, 1.4, 1, 1.4])
    hanh_dong = c1.selectbox('Hành động', ['Tất cả', 'Nhập', 'Xuất'])
    ngay_min, ngay_max = (df['Thời gian'].min().date(), df['Thời gian'].max().date())
    khoang_ngay = c2.date_input('Khoảng ngày', value=(ngay_min, ngay_max), min_value=ngay_min, max_value=ngay_max)
    o_loc = c3.selectbox('Ô', ['Tất cả'] + sorted(df['Mã ô'].dropna().unique()))
    tu_khoa = c4.text_input('Tìm (mã / tên / loại)')
    loc = df
    if hanh_dong != 'Tất cả':
        loc = loc[loc['Hành động'] == hanh_dong]
    if isinstance(khoang_ngay, tuple) and len(khoang_ngay) == 2:
        tu, den = khoang_ngay
        loc = loc[(loc['Thời gian'].dt.date >= tu) & (loc['Thời gian'].dt.date <= den)]
    if o_loc != 'Tất cả':
        loc = loc[loc['Mã ô'] == o_loc]
    if tu_khoa.strip():
        k = tu_khoa.strip().lower()
        loc = loc[loc[['Mã sản phẩm', 'Tên hàng', 'Loại']].astype(str).apply(lambda col: col.str.lower().str.contains(k, regex=False)).any(axis=1)]
    nhan_muc('Kết quả')
    st.markdown(html_the_so_lieu([('', len(loc), 'Số dòng hiển thị', 'theo bộ lọc hiện tại', 'blue'), ('nhap', int((loc['Hành động'] == 'Nhập').sum()), 'Lượt nhập', 'trong kết quả lọc', 'green'), ('xuat', int((loc['Hành động'] == 'Xuất').sum()), 'Lượt xuất', 'trong kết quả lọc', 'orange')]), unsafe_allow_html=True)
    hien_thi = loc[['Thời gian', 'Hành động', 'Mã sản phẩm', 'Mã ô', 'Tên hàng', 'Loại']].copy()
    hien_thi['Thời gian'] = hien_thi['Thời gian'].dt.strftime('%Y-%m-%d %H:%M:%S')
    st.dataframe(hien_thi, use_container_width=True, hide_index=True)
    st.download_button('Tải CSV (đang lọc)', hien_thi.to_csv(index=False).encode('utf-8-sig'), file_name='lich_su_kho.csv', mime='text/csv')
    nut_quay_lai()

# ============ CHỨC NĂNG: TẠO MÃ QR (TAB 1: SẢN PHẨM, TAB 2: VỊ TRÍ Ô) -> XUẤT FILE WORD ============

MAX_MA_QR = 1000

def tao_anh_qr_png(noi_dung):
    try:
        import qrcode
    except ImportError:
        qrcode = None
    if qrcode is not None:
        qr = qrcode.QRCode(error_correction=qrcode.constants.ERROR_CORRECT_M, box_size=10, border=4)
        qr.add_data(noi_dung)
        qr.make(fit=True)
        anh = qr.make_image(fill_color='black', back_color='white')
        bo_dem = io.BytesIO()
        anh.save(bo_dem)
        return bo_dem.getvalue()
    try:
        import cv2
    except ImportError:
        raise RuntimeError('Chưa cài thư viện tạo mã QR. Hãy chạy: pip install qrcode')
    ma_tran = cv2.QRCodeEncoder.create().encode(noi_dung)
    ma_tran = cv2.copyMakeBorder(ma_tran, 4, 4, 4, 4, cv2.BORDER_CONSTANT, value=255)
    ti_le = max(1, 400 // ma_tran.shape[0])
    ma_tran = cv2.resize(ma_tran, None, fx=ti_le, fy=ti_le, interpolation=cv2.INTER_NEAREST)
    return cv2.imencode('.png', ma_tran)[1].tobytes()

def _chuoi(v):
    return '' if v is None or (not isinstance(v, str) and pd.isna(v)) else str(v).strip()

def _so_nguyen(v):
    try:
        return None if v is None or pd.isna(v) else int(v)
    except (TypeError, ValueError):
        return None

def kiem_tra_bang_qr(cac_dong):
    ds, loi = ([], [])
    ten_loai_cua = {}
    ten_dd_cua = {}
    for i, d in enumerate(cac_dong, start=1):
        ten, loai = (_chuoi(d.get('Mã sản phẩm')), _chuoi(d.get('Mã loại sản phẩm')))
        ten_loai_dd = _chuoi(d.get('Tên loại sản phẩm'))
        ten_dd = _chuoi(d.get('Tên sản phẩm'))
        so_ke = _so_nguyen(d.get('Kệ'))
        bat_dau, so_luong = (_so_nguyen(d.get('STT bắt đầu')), _so_nguyen(d.get('Số lượng')))
        if not ten and (not ten_dd) and (not loai) and (not ten_loai_dd) and (so_luong is None):
            continue
        if so_ke is None or so_ke < 1 or so_ke > MAX_KE:
            loi.append(f'Dòng {i}: số kệ phải từ 1 đến {MAX_KE} (VD: 1 cho Kệ 1 → mã K1).')
            continue
        if st.session_state.get('kho') and (not any((lay_so_ke(k) == so_ke for k in st.session_state.kho))):
            loi.append(f'Dòng {i}: không có Kệ {so_ke} trong kho.')
            continue
        if not ten:
            loi.append(f'Dòng {i}: thiếu mã sản phẩm (3 ký tự, nằm trong mã QR, VD: RLY).')
            continue
        if not loai:
            loi.append(f'Dòng {i}: thiếu mã loại sản phẩm (3 ký tự, nằm trong mã QR, VD: ABC).')
            continue
        if not ma_hop_le(ten):
            loi.append(f"Dòng {i}: mã sản phẩm '{ten}' phải đúng 3 ký tự chữ hoặc số, không dấu (VD: RLY).")
            continue
        if not ma_hop_le(loai):
            loi.append(f"Dòng {i}: mã loại '{loai}' phải đúng 3 ký tự chữ hoặc số, không dấu (VD: ABC).")
            continue
        ten_dd = ten_dd or ten
        cu = ten_dd_cua.get(chuan_hoa(ten))
        if cu is not None and cu != ten_dd:
            loi.append(f"Dòng {i}: mã sản phẩm '{ten}' đã được dùng ở dòng trên với tên sản phẩm khác ('{cu}'). Mỗi mã sản phẩm chỉ có 1 tên sản phẩm.")
            continue
        ten_dd_cua[chuan_hoa(ten)] = ten_dd
        ten_loai_dd = ten_loai_dd or loai
        khoa_loai = (chuan_hoa(ten), chuan_hoa(loai))
        cu_loai = ten_loai_cua.get(khoa_loai)
        if cu_loai is not None and cu_loai != ten_loai_dd:
            loi.append(f"Dòng {i}: mã loại '{loai}' của mã sản phẩm '{ten}' đã được dùng ở dòng trên với tên loại khác ('{cu_loai}'). Mỗi mã loại chỉ có 1 tên loại.")
            continue
        ten_loai_cua[khoa_loai] = ten_loai_dd
        bat_dau = 1 if bat_dau is None else bat_dau
        if bat_dau < 1:
            loi.append(f'Dòng {i}: STT bắt đầu phải từ 1 trở lên.')
            continue
        if so_luong is None or so_luong < 1:
            loi.append(f'Dòng {i}: số lượng phải từ 1 trở lên.')
            continue
        if bat_dau + so_luong - 1 > STT_MAX:
            loi.append(f'Dòng {i}: STT vượt quá {STT_MAX} (STT bắt đầu {bat_dau} + số lượng {so_luong}). STT chỉ có 3 chữ số.')
            continue
        for stt in range(bat_dau, bat_dau + so_luong):
            ds.append({'ke': so_ke, 'ten': ten, 'ten_day_du': ten_dd, 'loai': loai, 'ten_loai_day_du': ten_loai_dd, 'stt': stt, 'noi_dung': ma_san_pham_tu_so_ke(so_ke, ten, loai, stt)})
    if not loi and (not ds):
        loi.append('Chưa có sản phẩm nào. Hãy nhập tên, loại, STT bắt đầu và số lượng.')
    if not loi and len(ds) > MAX_MA_QR:
        loi.append(f'Tổng cộng {len(ds)} mã, vượt giới hạn {MAX_MA_QR} mã mỗi lần. Hãy chia thành nhiều lần tạo.')
    return (ds, loi)

KHOANG_KHUNG_CM = 0.5

def so_module_qr(noi_dung):
    try:
        import qrcode
        qr = qrcode.QRCode(error_correction=qrcode.constants.ERROR_CORRECT_M, box_size=10, border=4)
        qr.add_data(noi_dung)
        qr.make(fit=True)
        return qr.modules_count
    except ImportError:
        pass
    import cv2
    return cv2.QRCodeEncoder.create().encode(noi_dung).shape[0]

def tao_anh_qr_cat_png(noi_dung):
    from PIL import Image
    goc = Image.open(io.BytesIO(tao_anh_qr_png(noi_dung))).convert('RGB')
    n = so_module_qr(noi_dung)
    le = round(4 * goc.width / (n + 8))
    bo_dem = io.BytesIO()
    goc.crop((le, le, goc.width - le, goc.height - le)).save(bo_dem, format='PNG')
    return bo_dem.getvalue()

def tinh_bo_cuc_tem(canh_khung_cm):
    rong_dung_duoc = 21.0 - 2 * 1.5
    rong_toi_thieu = max(canh_khung_cm + 0.5, 2.8)
    so_cot = max(1, int(rong_dung_duoc // rong_toi_thieu))
    return (so_cot, rong_dung_duoc / so_cot)

def tao_file_word_qr(ds_ma, kich_thuoc_cm=2.0, tieu_de='Tem QR sản phẩm'):
    from docx import Document
    from docx.enum.table import WD_ALIGN_VERTICAL, WD_TABLE_ALIGNMENT
    from docx.enum.text import WD_ALIGN_PARAGRAPH
    from docx.oxml import OxmlElement
    from docx.oxml.ns import qn
    from docx.shared import Cm, Pt, RGBColor, Twips
    LE, RONG_TRANG = (1.5, 21.0)
    kich_thuoc_qr = kich_thuoc_cm
    n_max = max((so_module_qr(m['noi_dung']) for m in ds_ma))
    n_min = min((so_module_qr(m['noi_dung']) for m in ds_ma))
    rong_qr_max = kich_thuoc_qr * n_max / (n_max + 8)
    rong_qr_min = kich_thuoc_qr * n_min / (n_min + 8)
    dai_nhat = max((len(m['noi_dung']) for m in ds_ma))
    co_chu = round(rong_qr_min * 72 / 2.54 / (0.56 * dai_nhat) * 2) / 2
    co_chu = max(3.5, min(co_chu, 14))
    rong_chu = max((len(m['noi_dung']) for m in ds_ma)) * co_chu * 0.6 / 72 * 2.54
    cao_noi_dung = rong_qr_max + (3 + co_chu * 1.2) / 72 * 2.54
    can_toi_thieu = max(rong_chu, cao_noi_dung) + 0.3
    rong_khung = max(2.5, math.ceil(can_toi_thieu * 2) / 2)
    so_cot, rong_cot = tinh_bo_cuc_tem(rong_khung)
    doc = Document()
    sec = doc.sections[0]
    sec.page_width, sec.page_height = (Cm(RONG_TRANG), Cm(29.7))
    sec.left_margin = sec.right_margin = Cm(LE)
    sec.top_margin = sec.bottom_margin = Cm(LE)
    sec.header_distance = Cm(0.7)
    normal = doc.styles['Normal']
    normal.font.name, normal.font.size = ('Arial', Pt(9))
    normal.element.rPr.rFonts.set(qn('w:eastAsia'), 'Arial')
    dau_trang = sec.header.paragraphs[0]
    chay = dau_trang.add_run(f"{tieu_de} — tạo ngày {datetime.now().strftime('%d/%m/%Y')} — {len(ds_ma)} mã")
    chay.font.size, chay.font.color.rgb = (Pt(8), RGBColor(128, 128, 128))
    so_hang = math.ceil(len(ds_ma) / so_cot)
    khung_tw = round(rong_khung * 567)
    khe_tw = round((rong_cot - rong_khung) / 2 * 567)
    bang = doc.add_table(rows=3 * so_hang, cols=3 * so_cot)
    bang.alignment = WD_TABLE_ALIGNMENT.CENTER
    bang.autofit = False
    tbl_pr = bang._tbl.tblPr
    tbl_w = tbl_pr.find(qn('w:tblW'))
    tbl_w.set(qn('w:type'), 'dxa')
    tbl_w.set(qn('w:w'), str((khung_tw + 2 * khe_tw) * so_cot))
    layout = tbl_pr.find(qn('w:tblLayout'))
    le_o = OxmlElement('w:tblCellMar')
    for canh in ('top', 'left', 'bottom', 'right'):
        e = OxmlElement(f'w:{canh}')
        e.set(qn('w:w'), '0')
        e.set(qn('w:type'), 'dxa')
        le_o.append(e)
    layout.addnext(le_o)
    for c, cot in enumerate(bang.columns):
        cot.width = Twips(khung_tw if c % 3 == 1 else khe_tw)

    def dat_o(o, vien, le_trai_phai=0):
        tc_pr = o._tc.get_or_add_tcPr()
        tc_w = tc_pr.find(qn('w:tcW'))
        vb = OxmlElement('w:tcBorders')
        for canh in ('top', 'left', 'bottom', 'right'):
            kieu, day, mau = vien.get(canh, ('nil', '0', 'auto'))
            e = OxmlElement(f'w:{canh}')
            for k, v in (('val', kieu), ('sz', day), ('space', '0'), ('color', mau)):
                e.set(qn(f'w:{k}'), v)
            vb.append(e)
        tc_w.addnext(vb)
        if le_trai_phai:
            mar = OxmlElement('w:tcMar')
            for canh in ('left', 'right'):
                e = OxmlElement(f'w:{canh}')
                e.set(qn('w:w'), str(le_trai_phai))
                e.set(qn('w:type'), 'dxa')
                mar.append(e)
            vb.addnext(mar)
        o.vertical_alignment = WD_ALIGN_VERTICAL.CENTER
    NET_DUT, NET_DEN = (('dashed', '4', 'A6A6A6'), ('single', '6', '000000'))
    for r, hang in enumerate(bang.rows):
        tr = hang._tr.get_or_add_trPr()
        tr.append(OxmlElement('w:cantSplit'))
        cao = OxmlElement('w:trHeight')
        cao.set(qn('w:val'), str(khung_tw if r % 3 == 1 else khe_tw))
        cao.set(qn('w:hRule'), 'exact')
        tr.append(cao)
        for c, o in enumerate(hang.cells):
            a_, b_ = (r % 3, c % 3)
            o.width = Twips(khung_tw if b_ == 1 else khe_tw)
            if a_ == 1 and b_ == 1:
                continue
            vien = {}
            if a_ == 0:
                vien['top'] = NET_DUT
            if a_ == 2:
                vien['bottom'] = NET_DUT
            if b_ == 0:
                vien['left'] = NET_DUT
            if b_ == 2:
                vien['right'] = NET_DUT
            dat_o(o, vien)
            p = o.paragraphs[0]
            p.paragraph_format.space_before = p.paragraph_format.space_after = Pt(0)
            p.paragraph_format.line_spacing = Pt(1)
            p.add_run().font.size = Pt(1)
    for k, ma in enumerate(ds_ma):
        o_trong = bang.cell(3 * (k // so_cot) + 1, 3 * (k % so_cot) + 1)
        dat_o(o_trong, {canh: NET_DEN for canh in ('top', 'left', 'bottom', 'right')}, le_trai_phai=85)
        p_anh = o_trong.paragraphs[0]
        p_anh.alignment = WD_ALIGN_PARAGRAPH.CENTER
        p_anh.paragraph_format.space_before = Pt(0)
        p_anh.paragraph_format.space_after = Pt(3)
        run_anh = p_anh.add_run()
        run_anh.font.size = Pt(1)
        run_anh.add_picture(io.BytesIO(tao_anh_qr_cat_png(ma['noi_dung'])), width=Cm(kich_thuoc_qr * so_module_qr(ma['noi_dung']) / (so_module_qr(ma['noi_dung']) + 8)))
        for inl in run_anh._r.findall('.//' + qn('wp:inline')):
            for a_ in ('distT', 'distB', 'distL', 'distR'):
                inl.set(a_, '0')
        p_chu = o_trong.add_paragraph()
        p_chu.alignment = WD_ALIGN_PARAGRAPH.CENTER
        p_chu.paragraph_format.space_before = p_chu.paragraph_format.space_after = Pt(0)
        r = p_chu.add_run(ma['noi_dung'])
        r.bold, r.font.size = (True, Pt(co_chu))
    zoom = doc.settings.element.find(qn('w:zoom'))
    if zoom is not None and zoom.get(qn('w:percent')) is None:
        zoom.set(qn('w:percent'), '100')
    bo_dem = io.BytesIO()
    doc.save(bo_dem)
    return bo_dem.getvalue()

def _tab_qr_san_pham():
    nhan_muc('Danh sách sản phẩm')
    bang = st.data_editor(pd.DataFrame([{'Kệ': 1, 'Tên sản phẩm': '', 'Mã sản phẩm': '', 'Tên loại sản phẩm': '', 'Mã loại sản phẩm': '', 'STT bắt đầu': 1, 'Số lượng': 10}]), num_rows='dynamic', use_container_width=True, hide_index=True, key='qr_bang', column_config={'Kệ': st.column_config.NumberColumn('Kệ (số)', min_value=1, max_value=MAX_KE, step=1, default=1, required=True, help='Mã kệ gồm 2 ký tự: K + số kệ (1-9). VD: 1 → K1'), 'Tên sản phẩm': st.column_config.TextColumn('Tên sản phẩm', help='Hiển thị trong ô / lịch sử khi quét nhập hàng. Bỏ trống thì hiển thị mã sản phẩm.'), 'Mã sản phẩm': st.column_config.TextColumn('Mã sản phẩm (3 ký tự)', required=True, max_chars=3, help='Đúng 3 ký tự chữ/số, nằm trong mã QR, VD: RLY → K1-RLY-ABC-001'), 'Tên loại sản phẩm': st.column_config.TextColumn('Tên loại sản phẩm', help='Hiển thị trong ô / lịch sử khi quét nhập hàng. Bỏ trống thì hiển thị mã loại.'), 'Mã loại sản phẩm': st.column_config.TextColumn('Mã loại sản phẩm (3 ký tự)', required=True, max_chars=3, help='Đúng 3 ký tự chữ/số, nằm trong mã QR, VD: ABC → K1-RLY-ABC-001'), 'STT bắt đầu': st.column_config.NumberColumn('STT bắt đầu', min_value=1, max_value=STT_MAX, step=1, default=1, help='STT 3 chữ số, từ 001 đến 999'), 'Số lượng': st.column_config.NumberColumn('Số lượng', min_value=1, step=1, default=10)})
    nhan_muc('Tùy chọn in')
    kich_thuoc = st.number_input('Kích thước mỗi mã QR khi in (cm)', min_value=1.5, max_value=6.0, value=2.0, step=0.5, key='qr_kich_thuoc')
    if st.button('Tạo mã QR & file Word', type='primary', use_container_width=True, key='qr_tao'):
        ds, loi = kiem_tra_bang_qr(bang.to_dict('records'))
        if loi:
            st.session_state.pop('qr_ket_qua', None)
            for l in loi:
                st.error(l)
        else:
            try:
                with st.spinner(f'Đang tạo {len(ds)} mã QR...'):
                    docx_bytes = tao_file_word_qr(ds, kich_thuoc)
                    anh_xem_truoc = [tao_anh_qr_png(m['noi_dung']) for m in ds[:8]]
            except ImportError:
                st.error('Chưa cài thư viện tạo file Word. Hãy chạy: `pip install python-docx` rồi khởi động lại app.')
            except RuntimeError as e:
                st.error(str(e))
            else:
                luu_ten_loai_day_du({(m['ten'], m['loai'], m['ten_loai_day_du']) for m in ds})
                luu_ten_day_du({(m['ten'], m['ten_day_du']) for m in ds})
                da_co = [m['noi_dung'] for m in ds if tim_san_pham_trong_kho(m['ten'], m['loai'], m['stt'])]
                st.session_state['qr_ket_qua'] = {'docx': docx_bytes, 'so_ma': len(ds), 'da_co': da_co, 'anh': anh_xem_truoc, 'nhan': [m['noi_dung'] for m in ds[:8]], 'ds': [m['noi_dung'] for m in ds], 'ten_file': f"ma_qr_san_pham_{datetime.now().strftime('%Y%m%d_%H%M%S')}.docx"}
    kq = st.session_state.get('qr_ket_qua')
    if kq:
        st.divider()
        st.success(f"Đã tạo **{kq['so_ma']}** mã QR. Tải file Word bên dưới rồi in ra dán lên sản phẩm.")
        if kq['da_co']:
            st.warning(f"Có {len(kq['da_co'])} mã **đang có sẵn trong kho** (nhập hàng sẽ bị chặn trùng): " + ', '.join((f'`{m}`' for m in kq['da_co'][:10])) + (' ...' if len(kq['da_co']) > 10 else ''))
        st.download_button('TẢI FILE WORD (.docx)', data=kq['docx'], file_name=kq['ten_file'], mime='application/vnd.openxmlformats-officedocument.wordprocessingml.document', type='primary', use_container_width=True, key='qr_tai')
        st.markdown('**Xem trước** (tối đa 8 mã đầu tiên):')
        st.image(kq['anh'], caption=kq['nhan'], width=130)
        with st.expander(f"Danh sách {kq['so_ma']} mã"):
            st.dataframe(pd.DataFrame({'Nội dung mã QR': kq['ds']}), use_container_width=True, hide_index=True)

# ============ TẠO MÃ QR — TAB 2: QR VỊ TRÍ MỖI Ô (theo các ô đang có trong kệ) ============

def _khoa_chon_o(ten_ke, h, c):
    return f'qroo_{ten_ke}_{h}_{c}'

def _chon_tat_ca_o_ke(ten_ke, gia_tri):
    ke = st.session_state.kho[ten_ke]
    for h in range(len(ke)):
        for c in range(len(ke[0])):
            st.session_state[_khoa_chon_o(ten_ke, h, c)] = gia_tri

def danh_sach_ma_o_da_chon(cac_ke):
    return [{'ten_ke': k, 'noi_dung': ma_o(k, h, c)} for k, h, c, _ in moi_o(cac_ke) if st.session_state.get(_khoa_chon_o(k, h, c), True)]

def _chon_tat_ca_ke(gia_tri):
    for k in st.session_state.kho:
        st.session_state[f'qro_chon_{k}'] = gia_tri

def _tab_qr_vi_tri_o():
    if not co_ke():
        return
    nhan_muc('Chọn kệ cần in')
    for k in st.session_state.kho:
        st.session_state.setdefault(f'qro_chon_{k}', True)
    c_het, c_bo = st.columns(2)
    c_het.button('Chọn tất cả', on_click=_chon_tat_ca_ke, args=(True,), use_container_width=True, key='qro_chon_het')
    c_bo.button('Bỏ chọn tất cả', on_click=_chon_tat_ca_ke, args=(False,), use_container_width=True, key='qro_bo_het')
    khung = st.container(height=280, border=True) if len(st.session_state.kho) > 6 else st.container(border=True)
    with khung:
        for k, ke in st.session_state.kho.items():
            st.checkbox(f'**{k}** — {len(ke)} hàng × {len(ke[0])} cột = {len(ke) * len(ke[0])} ô', key=f'qro_chon_{k}')
    cac_ke = [k for k in st.session_state.kho if st.session_state.get(f'qro_chon_{k}')]
    if cac_ke:
        nhan_muc('Chọn ô cần in')
        st.caption('Mặc định in tất cả ô của kệ đã chọn. Bỏ tích những ô không cần in.')
        for k in cac_ke:
            ke = st.session_state.kho[k]
            so_hang, so_cot = (len(ke), len(ke[0]))
            for h in range(so_hang):
                for c in range(so_cot):
                    st.session_state.setdefault(_khoa_chon_o(k, h, c), True)
            da_chon = sum((1 for h in range(so_hang) for c in range(so_cot) if st.session_state[_khoa_chon_o(k, h, c)]))
            with st.expander(f'{k} — đã chọn {da_chon}/{so_hang * so_cot} ô', expanded=len(cac_ke) == 1):
                b_het, b_bo = st.columns(2)
                b_het.button('Chọn hết ô', on_click=_chon_tat_ca_o_ke, args=(k, True), use_container_width=True, key=f'qroo_het_{k}')
                b_bo.button('Bỏ chọn hết ô', on_click=_chon_tat_ca_o_ke, args=(k, False), use_container_width=True, key=f'qroo_bo_{k}')
                for h in range(so_hang):
                    cols = st.columns([0.4] + [1] * so_cot)
                    cols[0].markdown(f'<div class="sodo-t">T{h + 1}</div>', unsafe_allow_html=True)
                    for c in range(so_cot):
                        cols[c + 1].checkbox(ma_o(k, h, c), key=_khoa_chon_o(k, h, c))
    else:
        st.warning('Chưa chọn kệ nào. Hãy tích chọn ít nhất 1 kệ trong danh sách.')
    ds = danh_sach_ma_o_da_chon(cac_ke)
    nhan_muc('Tùy chọn in')
    kich_thuoc = st.number_input('Kích thước mỗi mã QR khi in (cm)', min_value=1.5, max_value=6.0, value=2.0, step=0.5, key='qro_kich_thuoc')
    if st.button('Tạo QR ô & file Word', type='primary', use_container_width=True, key='qro_tao'):
        if not ds:
            st.session_state.pop('qro_ket_qua', None)
            st.error('Hãy chọn ít nhất 1 ô.' if cac_ke else 'Hãy chọn ít nhất 1 kệ.')
        elif len(ds) > MAX_MA_QR:
            st.session_state.pop('qro_ket_qua', None)
            st.error(f'Tổng cộng {len(ds)} mã, vượt giới hạn {MAX_MA_QR} mã mỗi lần. Hãy chọn ít ô hơn.')
        else:
            try:
                with st.spinner(f'Đang tạo {len(ds)} mã QR...'):
                    docx_bytes = tao_file_word_qr(ds, kich_thuoc, tieu_de='Tem QR vị trí ô')
                    anh_xem_truoc = [tao_anh_qr_png(m['noi_dung']) for m in ds[:8]]
            except ImportError:
                st.error('Chưa cài thư viện tạo file Word. Hãy chạy: `pip install python-docx` rồi khởi động lại app.')
            except RuntimeError as e:
                st.error(str(e))
            else:
                st.session_state['qro_ket_qua'] = {'docx': docx_bytes, 'so_ma': len(ds), 'anh': anh_xem_truoc, 'nhan': [m['noi_dung'] for m in ds[:8]], 'ds': [m['noi_dung'] for m in ds], 'ten_file': f"qr_vi_tri_o_{datetime.now().strftime('%Y%m%d_%H%M%S')}.docx"}
    kq = st.session_state.get('qro_ket_qua')
    if kq:
        st.divider()
        st.success(f"Đã tạo **{kq['so_ma']}** mã QR vị trí ô. Tải file Word bên dưới rồi in ra dán lên từng ô.")
        st.download_button('TẢI FILE WORD (.docx)', data=kq['docx'], file_name=kq['ten_file'], mime='application/vnd.openxmlformats-officedocument.wordprocessingml.document', type='primary', use_container_width=True, key='qro_tai')
        st.markdown('**Xem trước** (tối đa 8 mã đầu tiên):')
        st.image(kq['anh'], caption=kq['nhan'], width=130)
        with st.expander(f"Danh sách {kq['so_ma']} mã"):
            st.dataframe(pd.DataFrame({'Nội dung mã QR': kq['ds']}), use_container_width=True, hide_index=True)

def man_hinh_tao_qr():
    tieu_de_trang('Tạo mã QR')
    tab_sp, tab_o = st.tabs(['QR sản phẩm', 'QR vị trí ô'])
    with tab_sp:
        _tab_qr_san_pham()
    with tab_o:
        _tab_qr_vi_tri_o()
    nut_quay_lai()

# ============ CHỨC NĂNG: TẠO KỆ HÀNG ============

def man_hinh_tao_ke():
    tieu_de_trang('Quản lý kệ hàng')
    st.session_state.pop('tao_ke_tb', None)
    nhan_muc('Kệ hiện có')
    if co_ke():
        dong = []
        for ten_ke, ke in st.session_state.kho.items():
            so_hang, so_cot = (len(ke), len(ke[0]))
            dang_dung = sum((1 for hang in ke for o in hang for vt in o if vt is not None))
            so_vt = len(ke[0][0])
            dong.append({'Kệ': ten_ke, 'Số hàng': so_hang, 'Số cột': so_cot, 'Vị trí mỗi ô': so_vt, 'Tổng số ô': so_hang * so_cot, 'Vị trí đang dùng': f'{dang_dung}/{so_hang * so_cot * so_vt}'})
        st.dataframe(dong, use_container_width=True, hide_index=True)
    else:
        pass
    nhan_muc('Tạo kệ mới')
    c1, c2, c3 = st.columns(3)
    so_hang = int(c1.number_input('Số hàng (số tầng)', min_value=1, max_value=MAX_HANG, value=5, step=1, key='tao_ke_hang'))
    so_cot = int(c2.number_input('Số cột (số ô mỗi tầng)', min_value=1, max_value=MAX_COT, value=4, step=1, key='tao_ke_cot'))
    so_vt = int(c3.number_input('Số vị trí mỗi ô', min_value=1, max_value=MAX_VI_TRI, value=SO_VI_TRI, step=1, key='tao_ke_vt'))
    n = so_ke_tiep_theo()
    if n is None:
        st.warning(f'Đã đủ {MAX_KE} kệ (mã kệ chỉ có 2 ký tự: K1 đến K{MAX_KE}). Hãy xóa 1 kệ trống nếu muốn tạo kệ khác.')
    if st.button('Tạo kệ', type='primary', use_container_width=True, key='tao_ke_ok', disabled=n is None):
        ten_ke = them_ke(so_hang, so_cot, so_vt)
        st.session_state['tao_ke_tb'] = f'Đã tạo **{ten_ke}** ({so_hang} hàng × {so_cot} cột, mỗi ô {so_vt} vị trí). Bây giờ có thể nhập / xuất hàng.'
        st.rerun()
    if co_ke():
        nhan_muc('Sửa kệ')
        ten_sua = st.selectbox('Chọn kệ cần sửa', list(st.session_state.kho), key='sua_ke_chon')
        ke_sua = st.session_state.kho[ten_sua]
        h0, c0, v0 = (len(ke_sua), len(ke_sua[0]), len(ke_sua[0][0]))
        s1, s2, s3 = st.columns(3)
        h1 = int(s1.number_input('Số hàng (số tầng)', min_value=1, max_value=max(MAX_HANG, h0), value=h0, step=1, key=f'sua_hang_{ten_sua}'))
        c1_ = int(s2.number_input('Số cột (số ô mỗi tầng)', min_value=1, max_value=max(MAX_COT, c0), value=c0, step=1, key=f'sua_cot_{ten_sua}'))
        v1 = int(s3.number_input('Số vị trí mỗi ô', min_value=1, max_value=max(MAX_VI_TRI, v0), value=v0, step=1, key=f'sua_vt_{ten_sua}'))
        if (h1, c1_, v1) == (h0, c0, v0):
            co_the_sua = False
        else:
            ly_do = kiem_tra_sua_ke(ten_sua, h1, c1_, v1)
            if ly_do:
                for ld in ly_do:
                    st.warning(ld + ' Hãy xuất hàng ở đó trước.')
                co_the_sua = False
            else:
                co_the_sua = True
        if st.button('Lưu thay đổi', type='primary', use_container_width=True, disabled=not co_the_sua, key='sua_ke_btn'):
            ok, loi = sua_ke(ten_sua, h1, c1_, v1)
            if ok:
                st.session_state['tao_ke_tb'] = f'Đã sửa **{ten_sua}**: {h1} hàng × {c1_} cột × {v1} vị trí mỗi ô.'
                st.rerun()
            else:
                st.error(loi)
    if co_ke():
        nhan_muc('Xóa kệ')
        ten_xoa = st.selectbox('Chọn kệ cần xóa', list(st.session_state.kho), key='xoa_ke_chon')
        dang_dung = ke_dang_dung(ten_xoa)
        if dang_dung > 0:
            with st.container(key='xoa_ke_loi'):
                st.error(f'**{ten_xoa}** đang có sản phẩm không thể xóa.')
        else:
            xac_nhan = st.checkbox(f'Tôi chắc chắn muốn xóa {ten_xoa}', key=f'xoa_ke_ok_{ten_xoa}')
            if st.button(f'Xóa {ten_xoa}', use_container_width=True, disabled=not xac_nhan, key='xoa_ke_btn'):
                if xoa_ke(ten_xoa):
                    st.session_state['tao_ke_tb'] = f'Đã xóa **{ten_xoa}**.'
                    st.rerun()
    nut_quay_lai()

def man_hinh_tao_ke_dau_tien():
    _, giua, _ = st.columns([1, 2, 1])
    with giua:
        tieu_de_trang('Tạo kệ hàng đầu tiên')
        st.session_state.pop('tao_ke_tb', None)
        c1, c2, c3 = st.columns(3)
        so_hang = int(c1.number_input('Số hàng (số tầng)', min_value=1, max_value=MAX_HANG, value=5, step=1, key='bb_hang'))
        so_cot = int(c2.number_input('Số cột (số ô mỗi tầng)', min_value=1, max_value=MAX_COT, value=4, step=1, key='bb_cot'))
        so_vt = int(c3.number_input('Số vị trí mỗi ô', min_value=1, max_value=MAX_VI_TRI, value=SO_VI_TRI, step=1, key='bb_vt'))
        if st.button('Tạo kệ và vào trang chính', type='primary', use_container_width=True, key='bb_tao'):
            ten_ke = them_ke(so_hang, so_cot, so_vt)
            st.session_state['tb_trang_chu'] = f'Đã tạo **{ten_ke}** ({so_hang} hàng × {so_cot} cột, mỗi ô {so_vt} vị trí). Chào mừng bạn vào trang chính!'
            st.session_state.chuc_nang = None
            st.rerun()

# ============ ĐĂNG NHẬP / TẠO TÀI KHOẢN ============

def bam_mat_khau(mat_khau, muoi_hex):
    return hashlib.pbkdf2_hmac('sha256', mat_khau.encode('utf-8'), bytes.fromhex(muoi_hex), 200000).hex()

def tao_tai_khoan(ten, mat_khau, nhap_lai):
    ten = (ten or '').strip()
    if not re.fullmatch('[A-Za-z0-9_.\\-]{3,30}', ten):
        return (False, 'Tên tài khoản dài 3–30 ký tự, chỉ gồm chữ không dấu, số, dấu gạch dưới (_), gạch ngang (-) hoặc dấu chấm (.).')
    if len(mat_khau or '') < MK_TOI_THIEU:
        return (False, f'Mật khẩu phải có ít nhất {MK_TOI_THIEU} ký tự.')
    if mat_khau != nhap_lai:
        return (False, 'Hai lần nhập mật khẩu không giống nhau.')
    muoi = secrets.token_hex(16)
    if not them_tai_khoan(ten, muoi, bam_mat_khau(mat_khau, muoi)):
        return (False, f'Tên tài khoản **{ten}** đã có người dùng. Hãy chọn tên khác.')
    return (True, ten)

def kiem_tra_dang_nhap(ten, mat_khau):
    tk = lay_tai_khoan((ten or '').strip())
    muoi = tk['muoi'] if tk else '00' * 16
    bam = bam_mat_khau(mat_khau or '', muoi)
    if tk and hmac.compare_digest(bam, tk['mat_khau']):
        return tk['ten']
    return None

def _dang_nhap_thanh_cong(ten_hien_thi, ma_khoi_phuc_moi=None):
    st.session_state.clear()
    st.session_state['nguoi_dung'] = ten_hien_thi
    if ma_khoi_phuc_moi:
        st.session_state['_ma_kp_moi'] = ma_khoi_phuc_moi
    st.session_state['chuc_nang'] = None
    st.session_state['kho'] = doc_du_lieu(ten_hien_thi)
    st.session_state['_dat_cookie'] = tao_phien(ten_hien_thi)
    st.rerun()

# ---------- Mã khôi phục dạng QR ----------

QR_KP_TIEN_TO = 'STOCKLY-KP:'

def _noi_dung_qr_kp(ten, ma):
    return f'{QR_KP_TIEN_TO}{ten}:{_chuan_ma_kp(ma)}'

def doc_noi_dung_qr_kp(noi_dung):
    nd = (noi_dung or '').strip()
    if not nd.startswith(QR_KP_TIEN_TO):
        return None
    ten, _, ma = nd[len(QR_KP_TIEN_TO):].rpartition(':')
    ten, ma = (ten.strip(), _chuan_ma_kp(ma))
    return (ten, ma) if ten and len(ma) == KP_DO_DAI else None

def _co_opencv():
    import importlib.util
    return importlib.util.find_spec('cv2') is not None

def doc_qr_tu_anh(du_lieu):
    import cv2
    import numpy as np
    anh = cv2.imdecode(np.frombuffer(du_lieu, np.uint8), cv2.IMREAD_COLOR)
    if anh is None:
        return None
    anh = cv2.copyMakeBorder(anh, 40, 40, 40, 40, cv2.BORDER_CONSTANT, value=(255, 255, 255))
    may_quet = cv2.QRCodeDetector()
    for ti_le in (1.0, 2.0, 0.5, 1.5):
        th = anh if ti_le == 1.0 else cv2.resize(anh, None, fx=ti_le, fy=ti_le, interpolation=cv2.INTER_AREA if ti_le < 1 else cv2.INTER_CUBIC)
        try:
            noi_dung, _, _ = may_quet.detectAndDecode(th)
        except cv2.error:
            continue
        if noi_dung:
            return noi_dung
    return None

def _nhan_qr_khoi_phuc(noi_dung):
    kq = doc_noi_dung_qr_kp(noi_dung)
    if kq is None:
        st.error('Đây không phải mã QR khôi phục của Stockly. Hãy quét đúng mã QR bạn đã lưu khi tạo tài khoản.')
        return
    st.session_state['qm_quet'] = kq
    st.session_state['qm_cam'] = False
    st.rerun()

def man_hinh_quen_mat_khau():
    ss = st.session_state
    ket, quet = (ss.get('qm_ket_qua'), ss.get('qm_quet'))
    trang_thai = ['done', 'done', 'on'] if ket else ['done', 'on', ''] if quet else ['on', '', '']
    ten_buoc = ['Quét mã QR', 'Mật khẩu mới', 'Lưu mã QR mới']
    cac_buoc = ''.join((f'''<li class="{c}"><b>{(_svg_dn('ok') if c == 'done' else i)}</b><span>{t}</span></li>''' for i, (c, t) in enumerate(zip(trang_thai, ten_buoc), 1)))
    if ket:
        tieu, phu, cls, icon = ('Đã đặt lại mật khẩu', 'Mã QR khôi phục cũ đã hết hiệu lực. Hãy lưu mã QR mới ở bên dưới.', 'ok', 'ok')
    elif quet:
        tieu, phu, cls, icon = ('Đặt mật khẩu mới', f'Đã đọc mã QR của tài khoản <b>{_esc(quet[0])}</b>. Hãy nhập mật khẩu mới.', '', 'key')
    else:
        tieu, phu, cls, icon = ('Đặt lại mật khẩu', 'Quét mã QR khôi phục bạn đã lưu khi tạo tài khoản.', '', 'qr')
    st.markdown(_gon_html(f'<div class="qm-head"><div class="qm-ic {cls}">{_svg_dn(icon)}</div><div><div class="qm-t">{tieu}</div><div class="qm-s">{phu}</div></div></div><ol class="qm-steps">{cac_buoc}</ol>'), unsafe_allow_html=True)
    if ket:
        st.warning('**Hãy lưu mã QR khôi phục mới này ngay.** Mã chỉ hiện một lần, mã cũ không dùng được nữa.')
        _khung_ma_khoi_phuc(ket[1], ket[0], 'qm')
        st.caption('Giờ hãy chọn tab **Đăng nhập** để vào bằng mật khẩu mới.')
        if st.button('Tôi đã lưu mã QR', type='primary', use_container_width=True, key='qm_xong'):
            ss.pop('qm_ket_qua', None)
            st.rerun()
        return
    if quet:
        with st.form('form_quen_mk'):
            mk = st.text_input(f'Mật khẩu mới (tối thiểu {MK_TOI_THIEU} ký tự)', type='password', key='qm_mk', placeholder='Nhập mật khẩu mới')
            mk2 = st.text_input('Nhập lại mật khẩu mới', type='password', key='qm_mk2', placeholder='Nhập lại mật khẩu mới')
            gui = st.form_submit_button('Đặt lại mật khẩu', type='primary', use_container_width=True)
        if gui:
            ok, kq = dat_lai_mat_khau_bang_ma(quet[0], quet[1], mk, mk2)
            if ok:
                ss.pop('qm_quet', None)
                ss['qm_ket_qua'] = (quet[0], kq)
                st.rerun()
            st.error(kq)
        if st.button('Quét lại mã QR', use_container_width=True, key='qm_quet_lai'):
            ss.pop('qm_quet', None)
            st.rerun()
        st.caption(f'Nhập sai mã {KP_SAI_TOI_DA} lần sẽ bị tạm khóa {KP_KHOA_GIAY // 60} phút.')
        return
    cach = 'Dùng camera'
    if _co_opencv():
        cach = st.radio('Cách quét', ['Dùng camera', 'Tải ảnh QR lên'], horizontal=True, key='qm_cach', label_visibility='collapsed')
    if cach == 'Dùng camera':
        if ss.get('qm_cam'):
            if _QR_LIVE is None:
                st.error('Không tạo được thành phần quét QR bằng camera.')
            else:
                kq_cam = _QR_LIVE(key='qm_scan', default=None)
                if isinstance(kq_cam, dict) and kq_cam.get('id') and (kq_cam['id'] != ss.get('qm_scan_id')):
                    ss['qm_scan_id'] = kq_cam['id']
                    _nhan_qr_khoi_phuc(kq_cam.get('code'))
            if st.button('Tắt camera', use_container_width=True, key='qm_tat_cam'):
                ss['qm_cam'] = False
                st.rerun()
        elif st.button('Bật camera để quét mã QR', type='primary', use_container_width=True, key='qm_bat_cam'):
            ss['qm_cam'] = True
            st.rerun()
    else:
        ss['qm_cam'] = False
        tep = st.file_uploader('Ảnh mã QR khôi phục (PNG / JPG)', type=['png', 'jpg', 'jpeg'], key='qm_anh')
        if tep is not None:
            try:
                noi_dung = doc_qr_tu_anh(tep.getvalue())
            except Exception:
                noi_dung = None
            if noi_dung is None:
                st.error('Không đọc được mã QR trong ảnh. Hãy dùng ảnh rõ nét, đủ sáng và thấy trọn mã QR.')
            else:
                _nhan_qr_khoi_phuc(noi_dung)
    st.markdown(_gon_html(f"""<div class="qm-help">{_svg_dn('lock')}<div><b>Mất cả mật khẩu lẫn mã QR khôi phục?</b> Stockly không tự đặt lại mật khẩu chỉ dựa vào tên tài khoản. Hãy liên hệ quản trị viên để được xác minh danh tính và hỗ trợ.</div></div>"""), unsafe_allow_html=True)

def _khung_ma_khoi_phuc(ma, ten, key):
    try:
        png = tao_anh_qr_png(_noi_dung_qr_kp(ten, ma))
    except RuntimeError as loi:
        st.warning(f'{loi} Tạm thời hãy lưu mã dạng chữ bên dưới.')
        st.code(ma, language=None)
        return
    st.image(png, width=240, caption=f'Mã QR khôi phục của tài khoản {ten}')
    st.download_button('Tải mã QR về máy (.png)', data=png, file_name=f'stockly_khoi_phuc_{ten}.png', mime='image/png', use_container_width=True, key=f'{key}_tai')

def hien_ma_khoi_phuc_moi():
    ma = st.session_state.get('_ma_kp_moi')
    if not ma:
        return
    with st.container(border=True):
        st.warning('**Hãy lưu lại mã QR khôi phục này.** Mã chỉ hiện MỘT lần. Nếu quên mật khẩu, bạn quét mã QR này để đặt lại mật khẩu. Ai có mã QR này đều đặt lại được mật khẩu của bạn, hãy cất kỹ và đừng gửi cho người khác.')
        _khung_ma_khoi_phuc(ma, st.session_state.get('nguoi_dung', ''), 'kp_moi')
        if st.button('Tôi đã lưu mã QR', type='primary', use_container_width=True, key='kp_da_luu'):
            st.session_state.pop('_ma_kp_moi', None)
            st.rerun()

def man_hinh_ma_khoi_phuc():
    tieu_de_trang('Mã QR khôi phục')
    ten = st.session_state.nguoi_dung
    if co_ma_khoi_phuc(ten):
        st.info('Tài khoản đã có mã QR khôi phục. Vì bảo mật, mã cũ không xem lại được. Nếu mất mã, hãy tạo mã mới (mã cũ sẽ hết hiệu lực).')
    else:
        st.warning('Tài khoản này **chưa có mã QR khôi phục**, nếu quên mật khẩu sẽ không lấy lại được. Hãy tạo mã ngay.')
    with st.form('form_kp'):
        mk = st.text_input('Nhập mật khẩu hiện tại để xác nhận', type='password', key='kp_mk')
        gui = st.form_submit_button('Tạo mã QR khôi phục mới', type='primary', use_container_width=True)
    if gui:
        if kiem_tra_dang_nhap(ten, mk):
            st.session_state['kp_trang_ma'] = tao_ma_khoi_phuc(ten)
        else:
            st.session_state.pop('kp_trang_ma', None)
            st.error('Mật khẩu không đúng.')
    ma = st.session_state.get('kp_trang_ma')
    if ma:
        st.success('Đã tạo mã QR khôi phục mới. Hãy lưu lại ngay, rời trang này sẽ không xem lại được.')
        _khung_ma_khoi_phuc(ma, ten, 'kp_trang')
    nut_quay_lai()

# ============ GIAO DIỆN MÀN HÌNH ĐĂNG NHẬP ============

_SVG_DN = {'qr': '<path d="M4 8V6a2 2 0 0 1 2-2h2M16 4h2a2 2 0 0 1 2 2v2M20 16v2a2 2 0 0 1-2 2h-2M8 20H6a2 2 0 0 1-2-2v-2"/><path d="M8 12h8"/>', 'grid': '<rect x="3" y="3" width="7" height="7" rx="1.6"/><rect x="14" y="3" width="7" height="7" rx="1.6"/><rect x="3" y="14" width="7" height="7" rx="1.6"/><rect x="14" y="14" width="7" height="7" rx="1.6"/>', 'hist': '<path d="M3 12a9 9 0 1 0 3-6.7L3 8"/><path d="M3 3v5h5"/><path d="M12 7v5l3 2"/>', 'lock': '<rect x="4" y="11" width="16" height="10" rx="2"/><path d="M8 11V7a4 4 0 0 1 8 0v4"/>', 'key': '<circle cx="7.5" cy="15.5" r="5.5"/><path d="m21 2-9.6 9.6"/><path d="m15.5 7.5 3 3L22 7l-3-3"/>', 'ok': '<path d="M20 6 9 17l-5-5"/>'}

def _svg_dn(ten):
    return f'<svg viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="1.8" stroke-linecap="round" stroke-linejoin="round" aria-hidden="true">{_SVG_DN[ten]}</svg>'

_TEN_ANH_KHO = ('kho_3d.png', 'kho_3d.jpg', 'kho_3d.jpeg', 'kho_3d.webp')

@st.cache_resource(show_spinner=False)
def _anh_kho_data_uri():
    try:
        from PIL import Image
        for ten in _TEN_ANH_KHO:
            f = Path(__file__).with_name(ten)
            if f.exists():
                im = Image.open(f).convert('RGB')
                if im.width > 1100:
                    im = im.resize((1100, round(im.height * 1100 / im.width)))
                buf = io.BytesIO()
                im.save(buf, format='JPEG', quality=86, optimize=True)
                return 'data:image/jpeg;base64,' + base64.b64encode(buf.getvalue()).decode('ascii')
    except Exception:
        pass
    return ''

_ICON_NGUOI = 'url("data:image/svg+xml,%3Csvg%20xmlns=\'http://www.w3.org/2000/svg\'%20viewBox=\'0%200%2024%2024\'%20fill=\'none\'%20stroke=\'%237b8aa8\'%20stroke-width=\'1.8\'%20stroke-linecap=\'round\'%20stroke-linejoin=\'round\'%3E%3Ccircle%20cx=\'12\'%20cy=\'8\'%20r=\'4\'/%3E%3Cpath%20d=\'M4%2021a8%208%200%200%201%2016%200\'/%3E%3C/svg%3E")'

_ICON_KHOA = 'url("data:image/svg+xml,%3Csvg%20xmlns=\'http://www.w3.org/2000/svg\'%20viewBox=\'0%200%2024%2024\'%20fill=\'none\'%20stroke=\'%237b8aa8\'%20stroke-width=\'1.8\'%20stroke-linecap=\'round\'%20stroke-linejoin=\'round\'%3E%3Crect%20x=\'4\'%20y=\'11\'%20width=\'16\'%20height=\'10\'%20rx=\'2\'/%3E%3Cpath%20d=\'M8%2011V7a4%204%200%200%201%208%200v4\'/%3E%3C/svg%3E")'

CSS_DANG_NHAP = """
<style>
[data-testid="stAppViewContainer"]{
  background-image:
    radial-gradient(760px 460px at 100% 0%, rgba(96,165,250,.38), transparent 65%),
    radial-gradient(820px 520px at 0% 0%, rgba(26,60,156,.30), transparent 65%),
    radial-gradient(640px 400px at 0% 100%, rgba(238,122,20,.38), transparent 65%),
    radial-gradient(720px 440px at 100% 100%, rgba(96,165,250,.26), transparent 65%) !important; }
[data-testid="stMainBlockContainer"], .block-container{ max-width:1160px; padding-top:3.5vh; }

/* ---- khung 2 cột: thương hiệu (trái) + biểu mẫu (phải) ---- */
div[data-testid="stHorizontalBlock"]:has(.lg-brand){
  gap:0 !important; max-width:1060px; margin:0 auto; align-items:stretch !important;
  border:1px solid rgba(255,255,255,.65); border-radius:26px; overflow:hidden; background:var(--paper);
  box-shadow:0 40px 80px -32px rgba(10,25,80,.55), 0 3px 10px rgba(10,25,80,.10); }
div[data-testid="stHorizontalBlock"]:has(.lg-brand) > div[data-testid="stColumn"]{ min-width:0 !important; width:auto !important; }
div[data-testid="stHorizontalBlock"]:has(.lg-brand) > div[data-testid="stColumn"]:first-child{
  flex:1.1 1 0 !important; padding:34px 40px 28px; color:#fff;
  background:
    radial-gradient(520px 340px at 94% 0%, rgba(34,211,238,.30), transparent 62%),
    radial-gradient(480px 340px at 0% 104%, rgba(238,122,20,.32), transparent 60%),
    radial-gradient(520px 260px at 100% 104%, rgba(34,211,238,.34), transparent 62%),
    repeating-linear-gradient(0deg, rgba(255,255,255,.05) 0 1px, transparent 1px 38px),
    repeating-linear-gradient(90deg, rgba(255,255,255,.05) 0 1px, transparent 1px 38px),
    linear-gradient(155deg, #0a1b52 0%, #12296e 44%, #1a3c9c 100%); }
div[data-testid="stHorizontalBlock"]:has(.lg-brand) > div[data-testid="stColumn"]:last-child{
  flex:1 1 0 !important; padding:44px 42px; display:flex; flex-direction:column; justify-content:center;
  background:radial-gradient(440px 280px at 100% 0%, rgba(26,60,156,.08), transparent 70%), var(--paper); }

/* ---- cột trái: logo + tiêu đề / ảnh kệ kho / 3 thẻ tính năng ---- */
.lg-brand{ display:flex; flex-direction:column; justify-content:space-between; gap:16px; min-height:720px; }
.lg-top{ display:flex; align-items:center; gap:14px; }
.lg-top img{ filter:drop-shadow(0 6px 14px rgba(0,0,0,.35)); }
.lg-vbar{ width:1px; height:30px; background:rgba(255,255,255,.28); }
.lg-top span{ font:600 .82rem/1.2 var(--f-ui); letter-spacing:.16em; text-transform:uppercase; color:rgba(255,255,255,.78); }
.lg-h{ margin-top:22px; font:700 clamp(1.9rem,3.1vw,2.55rem)/1.06 var(--f-head); color:#fff; letter-spacing:.2px; }
.lg-h em{ font-style:normal; color:#fff; }
.lg-bar{ width:54px; height:3px; margin:14px 0 12px; border-radius:3px; background:linear-gradient(90deg,#ee7a14,#fbbf24); }
.lg-p{ font:400 .96rem/1.5 var(--f-ui); color:rgba(255,255,255,.80); }

.lg-hero{ flex:1; display:flex; align-items:center; justify-content:center; margin:0 -40px; min-height:250px; }
.lg-hero img{ display:block; width:100%; height:auto; max-height:360px; object-fit:cover;
  -webkit-mask-image:radial-gradient(ellipse 72% 70% at 52% 50%, #000 42%, transparent 100%);
          mask-image:radial-gradient(ellipse 72% 70% at 52% 50%, #000 42%, transparent 100%); }
.lg-hero.alt{ margin:0; }

.lg-tiles{ display:grid; grid-template-columns:repeat(3,1fr); gap:12px; }
.lg-tile{ padding:13px 14px 14px; border-radius:15px; background:rgba(255,255,255,.08); border:1px solid rgba(255,255,255,.17);
  backdrop-filter:blur(6px); box-shadow:0 16px 34px -22px rgba(0,0,0,.65); }
.lg-fi{ width:36px; height:36px; border-radius:11px; display:grid; place-items:center; color:#7dd3fc; margin-bottom:9px;
  background:rgba(255,255,255,.10); border:1px solid rgba(255,255,255,.20); }
.lg-fi svg{ width:20px; height:20px; }
.lg-tile b{ display:block; font:600 .98rem/1.2 var(--f-ui); color:#fff; }
.lg-tile span{ display:block; margin-top:4px; font:400 .8rem/1.35 var(--f-ui); color:rgba(255,255,255,.70); }
.lg-foot{ font:400 .82rem var(--f-ui); color:rgba(255,255,255,.55); }

/* sơ đồ kệ minh họa (chỉ hiện khi không có ảnh kho_3d) */
.lg-card{ width:100%; padding:14px 16px; border-radius:16px; background:rgba(255,255,255,.07); border:1px solid rgba(255,255,255,.17); }
.lg-card-h{ display:flex; justify-content:space-between; align-items:center; margin-bottom:10px; font:600 1rem var(--f-ui); color:#fff; }
.lg-card-h span{ font-size:.72rem; letter-spacing:.12em; text-transform:uppercase; color:rgba(255,255,255,.62);
  border:1px solid rgba(255,255,255,.25); border-radius:99px; padding:2px 9px; }
.lg-rack{ display:grid; grid-template-columns:24px repeat(8,1fr); gap:5px; align-items:center; }
.lg-rack b{ font:600 .72rem var(--f-ui); color:rgba(255,255,255,.55); }
.lg-rack i{ display:block; height:22px; border-radius:5px; background:rgba(255,255,255,.08); border:1px solid rgba(255,255,255,.16); }
.lg-rack i.f{ background:linear-gradient(180deg,#fbbf24,#ee7a14); border-color:rgba(255,255,255,.35); }
.lg-rack i.h{ background:linear-gradient(180deg,#a5f3fc,#22d3ee); border-color:#fff; box-shadow:0 0 0 3px rgba(34,211,238,.35), 0 0 16px rgba(34,211,238,.7); }
.lg-card-f{ display:flex; flex-wrap:wrap; align-items:center; gap:6px 16px; margin-top:12px; font:500 .85rem var(--f-ui); color:rgba(255,255,255,.78); }
.lg-card-f .d{ display:inline-block; width:10px; height:10px; border-radius:3px; margin-right:6px; vertical-align:-1px; background:rgba(255,255,255,.12); border:1px solid rgba(255,255,255,.35); }
.lg-card-f .d.f{ background:#f59e0b; border-color:#f59e0b; } .lg-card-f .d.h{ background:#22d3ee; border-color:#22d3ee; }
.lg-chip{ margin-left:auto; padding:3px 10px; border-radius:7px; background:rgba(0,0,0,.28); border:1px solid rgba(255,255,255,.22);
  font:600 .88rem var(--f-ui); letter-spacing:.07em; color:#fff; }

/* ---- cột phải: biểu mẫu ---- */
.lg-kicker{ display:inline-block; font:700 .8rem var(--f-ui); letter-spacing:.16em; text-transform:uppercase; color:#ee7a14; }
.lg-kicker::before{ content:""; display:inline-block; width:26px; height:3px; border-radius:2px; background:#ee7a14; margin-right:10px; vertical-align:middle; }
.lg-wt{ margin-top:10px; font:700 clamp(1.9rem,3vw,2.5rem)/1.08 var(--f-head); color:var(--ink); }
.lg-ws{ margin:8px 0 10px; font:400 1.02rem/1.45 var(--f-ui); color:var(--muted); }
.lg-note{ display:flex; gap:10px; align-items:center; margin-top:18px; padding-top:14px; border-top:1px dashed var(--line);
  font:400 .9rem/1.45 var(--f-ui); color:var(--muted); }
.lg-note svg{ flex:none; width:18px; height:18px; color:#1a3c9c; }

/* tab dạng thanh chọn: tab đang chọn nền cam nhạt + gạch cam */
div[data-testid="stHorizontalBlock"]:has(.lg-brand) div[data-baseweb="tab-list"]{
  gap:6px; padding:5px; background:rgba(26,60,156,.07); border-radius:14px; }
div[data-testid="stHorizontalBlock"]:has(.lg-brand) button[data-baseweb="tab"]{
  flex:1 1 0; justify-content:center; height:46px; border-radius:10px; color:var(--muted); background:transparent; }
div[data-testid="stHorizontalBlock"]:has(.lg-brand) button[data-baseweb="tab"] p{ font-size:1.05rem; font-weight:600; }
div[data-testid="stHorizontalBlock"]:has(.lg-brand) button[data-baseweb="tab"][aria-selected="true"]{
  background:rgba(238,122,20,.13); color:#ee7a14; box-shadow:inset 0 -3px 0 #ee7a14; }
div[data-testid="stHorizontalBlock"]:has(.lg-brand) button[data-baseweb="tab"][aria-selected="true"] p{ color:#ee7a14; }
div[data-testid="stHorizontalBlock"]:has(.lg-brand) [data-baseweb="tab-highlight"],
div[data-testid="stHorizontalBlock"]:has(.lg-brand) [data-baseweb="tab-border"]{ display:none; }

/* ô nhập: có biểu tượng người / khóa bên trái */
div[data-testid="stHorizontalBlock"]:has(.lg-brand) div[data-testid="stForm"]{ background:transparent; border:0; padding:0; }
div[data-testid="stHorizontalBlock"]:has(.lg-brand) div[data-testid="stTextInput"] input{
  min-height:48px; border-radius:10px; background-repeat:no-repeat; background-position:15px center; background-size:20px; }
.st-key-dn_ten input, .st-key-tk_ten input{ padding-left:46px !important; background-image:__ICON_NGUOI__; }
.st-key-dn_mk input, .st-key-tk_mk input, .st-key-tk_mk2 input, .st-key-qm_mk input, .st-key-qm_mk2 input{ padding-left:46px !important; background-image:__ICON_KHOA__; }
div[data-testid="stHorizontalBlock"]:has(.lg-brand) div[data-testid="stFormSubmitButton"] > button{
  min-height:50px; border-radius:10px; font-size:1.05rem; letter-spacing:.02em; }
div[data-testid="stHorizontalBlock"]:has(.lg-brand) div[data-testid="stFormSubmitButton"] > button[kind^="primary"],
div[data-testid="stHorizontalBlock"]:has(.lg-brand) div[data-testid="stFormSubmitButton"] > button[data-testid^="stBaseButton-primary"]{
  background-image:linear-gradient(135deg,#12296e 0%,#1a3c9c 55%,#2f66d9 100%); border:0;
  box-shadow:0 10px 22px -10px rgba(26,60,156,.75); }
div[data-testid="stHorizontalBlock"]:has(.lg-brand) div[data-testid="stFormSubmitButton"] > button:hover{
  filter:brightness(1.08); box-shadow:0 14px 26px -10px rgba(26,60,156,.85); }

/* nút chuyển màn: Tạo tài khoản / Quên mật khẩu? / Quay lại đăng nhập */
.st-key-dn_vao_tao button, .st-key-dn_vao_quen button, .st-key-dn_quay_lai button{
  min-height:48px; border-radius:10px; font-size:1rem; font-weight:600; background:var(--paper); border:1px solid var(--line); color:var(--ink); }
.st-key-dn_vao_tao button, .st-key-dn_vao_quen button{ min-height:38px; padding:.3rem .9rem; font-size:.95rem; border-radius:9px; }
.st-key-dn_vao_tao, .st-key-dn_vao_quen{ margin-top:10px; }
.st-key-dn_vao_tao button:hover, .st-key-dn_vao_quen button:hover, .st-key-dn_quay_lai button:hover{
  border-color:#1a3c9c; color:#1a3c9c; background:rgba(26,60,156,.06); }

/* ---- Quên mật khẩu: tiêu đề, 3 bước, ô nhập mã, ghi chú ---- */
.qm-head{ display:flex; gap:14px; align-items:center; margin:8px 0 14px; }
.qm-ic{ flex:none; width:48px; height:48px; border-radius:14px; display:grid; place-items:center; background:rgba(26,60,156,.10); color:#1a3c9c; }
.qm-ic.ok{ background:rgba(15,118,110,.12); color:#0f766e; }
.qm-ic svg{ width:24px; height:24px; }
.qm-t{ font:700 1.3rem/1.2 var(--f-head); color:var(--ink); }
.qm-s{ margin-top:3px; font:400 .95rem/1.45 var(--f-ui); color:var(--muted); }
.qm-steps{ display:flex; gap:8px; margin:0 0 16px; padding:0; list-style:none; }
.qm-steps li{ flex:1 1 0; min-width:0; display:flex; align-items:center; gap:8px; padding:8px 10px; border:1px solid var(--line);
  border-radius:10px; background:var(--paper); font:500 .82rem/1.25 var(--f-ui); color:var(--muted); }
.qm-steps li b{ flex:none; width:22px; height:22px; border-radius:50%; display:grid; place-items:center;
  font:700 .76rem var(--f-ui); background:rgba(26,60,156,.10); color:#1a3c9c; }
.qm-steps li b svg{ width:13px; height:13px; }
.qm-steps li.on{ color:var(--ink); border-color:rgba(26,60,156,.35); background:rgba(26,60,156,.05); }
.qm-steps li.on b{ background:#1a3c9c; color:#fff; }
.qm-steps li.done{ color:var(--ink); }
.qm-steps li.done b{ background:#0f766e; color:#fff; }
.qm-help{ display:flex; gap:10px; align-items:flex-start; margin-top:16px; padding:12px 14px; border-radius:12px;
  background:rgba(238,122,20,.08); border:1px solid rgba(238,122,20,.28); font:400 .9rem/1.5 var(--f-ui); color:var(--ink); }
.qm-help svg{ flex:none; width:18px; height:18px; margin-top:2px; color:#ee7a14; }
.st-key-qm_xong button, .st-key-qm_bat_cam button, .st-key-qm_tat_cam button, .st-key-qm_quet_lai button{ min-height:50px; border-radius:10px; font-size:1.05rem; }
@media (max-width:520px){ .qm-steps li span{ display:none; } .qm-steps li{ justify-content:center; } }

/* ---- màn hình hẹp: xếp dọc, thu gọn phần thương hiệu ---- */
@media (max-width:860px){
  div[data-testid="stHorizontalBlock"]:has(.lg-brand){ flex-wrap:wrap !important; border-radius:20px; }
  div[data-testid="stHorizontalBlock"]:has(.lg-brand) > div[data-testid="stColumn"]{ flex:1 1 100% !important; min-width:100% !important; }
  div[data-testid="stHorizontalBlock"]:has(.lg-brand) > div[data-testid="stColumn"]:first-child{ padding:24px 22px; }
  div[data-testid="stHorizontalBlock"]:has(.lg-brand) > div[data-testid="stColumn"]:last-child{ padding:26px 20px 28px; }
  .lg-brand{ min-height:0; gap:12px; }
  .lg-hero, .lg-tiles, .lg-p, .lg-foot, .lg-bar{ display:none; }
  .lg-h{ font-size:1.7rem; margin-top:14px; }
}
</style>
""".replace("__ICON_NGUOI__", _ICON_NGUOI).replace("__ICON_KHOA__", _ICON_KHOA)

_RACK_MINH_HOA = [('T3', 'ff.f.fff'), ('T2', 'f.ffh.f.'), ('T1', 'ffff.ff.')]

def _html_rack_du_phong():
    hang = ''
    for nhan, mau in _RACK_MINH_HOA:
        hang += f'<b>{nhan}</b>' + ''.join((f'''<i class="{(c if c != '.' else '')}"></i>''' for c in mau))
    return f'<div class="lg-hero alt"><div class="lg-card"><div class="lg-card-h"><b>Kệ K1</b><span>Minh họa</span></div><div class="lg-rack">{hang}</div><div class="lg-card-f"><span><i class="d f"></i>Có hàng</span><span><i class="d"></i>Trống</span><span><i class="d h"></i>Vừa quét</span><span class="lg-chip">K1-RLY-ABC-001</span></div></div></div>'

def html_thuong_hieu_dang_nhap():
    anh = _anh_kho_data_uri()
    hero = f'<div class="lg-hero"><img src="{anh}" alt=""></div>' if anh else _html_rack_du_phong()
    diem = [('qr', 'Quét QR nhập / xuất', 'Ghi nhận hàng vào ra chỉ với một lần quét.'), ('grid', 'Sơ đồ kệ trực quan', 'Biết ngay ô nào còn trống, ô nào đã đầy.'), ('hist', 'Lịch sử đầy đủ', 'Mọi thao tác nhập / xuất đều được lưu để tra cứu.')]
    the = ''.join((f'<div class="lg-tile"><div class="lg-fi">{_svg_dn(k)}</div><b>{t}</b><span>{m}</span></div>' for k, t, m in diem))
    return _gon_html(f'\n    <div class="lg-brand">\n      <div>\n        <div class="lg-top">{html_logo(54)}<i class="lg-vbar"></i><span>Quản lý kho thông minh</span></div>\n        <div class="lg-h">Kiểm soát kho hàng<br>chính xác đến <em>từng ô</em></div>\n        <div class="lg-bar"></div>\n        <div class="lg-p">Nhập, xuất và tra cứu hàng hóa nhanh chóng bằng mã QR.<br>Mỗi vị trí trên kệ đều có mã riêng, dễ tìm và không nhầm lẫn.</div>\n      </div>\n      {hero}\n      <div class="lg-tiles">{the}</div>\n      <div class="lg-foot">© {datetime.now().year} Stockly. Mọi quyền được bảo lưu.</div>\n    </div>\n    ')

_TIEU_DE_DANG_NHAP = {'dang_nhap': ('Cổng đăng nhập', 'Chào mừng đến với Stockly', ''), 'tao': ('Tạo tài khoản', 'Tạo tài khoản mới', ''), 'quen': ('Khôi phục tài khoản', 'Quên mật khẩu?', '')}

def html_chao_dang_nhap(man='dang_nhap'):
    nho, lon, mota = _TIEU_DE_DANG_NHAP.get(man, _TIEU_DE_DANG_NHAP['dang_nhap'])
    return _gon_html(f'\n    <div class="lg-kicker">{nho}</div>\n    <div class="lg-wt">{lon}</div>\n    <div class="lg-ws">{mota}</div>\n    ')

def html_ghi_chu_dang_nhap():
    chu = f'Nhập sai mật khẩu {SAI_TOI_DA} lần sẽ bị tạm khóa {KHOA_GIAY} giây.'
    return _gon_html(f"""<div class="lg-note">{_svg_dn('lock')}<div>{chu}</div></div>""")

def _chuyen_man_dang_nhap(man):
    st.session_state['dn_view'] = man
    st.rerun()

def _nut_ve_dang_nhap():
    if st.button('Quay lại đăng nhập', use_container_width=True, key='dn_quay_lai', **icon_kw('arrow_back')):
        _chuyen_man_dang_nhap('dang_nhap')

def man_hinh_dang_nhap():
    st.markdown(_gon_html('<style>.st-key-dang_xuat button{ min-height:40px !important; }</style>'), unsafe_allow_html=True)
    st.markdown(_gon_html(CSS_DANG_NHAP), unsafe_allow_html=True)
    cot_trai, giua = st.columns([1.12, 1], gap='small')
    with cot_trai:
        st.markdown(html_thuong_hieu_dang_nhap(), unsafe_allow_html=True)
    with giua:
        man = st.session_state.get('dn_view', 'dang_nhap')
        st.markdown(html_chao_dang_nhap(man), unsafe_allow_html=True)
        if man == 'tao':
            with st.form('form_tao_tai_khoan'):
                ten_moi = st.text_input('Tên tài khoản mới', key='tk_ten', placeholder='Nhập tên tài khoản', help='3–30 ký tự: chữ không dấu, số, _ - . (phân biệt chữ hoa / chữ thường)')
                mk_moi = st.text_input(f'Mật khẩu (tối thiểu {MK_TOI_THIEU} ký tự)', type='password', key='tk_mk', placeholder='Nhập mật khẩu')
                mk_lai = st.text_input('Nhập lại mật khẩu', type='password', key='tk_mk2', placeholder='Nhập lại mật khẩu')
                tao = st.form_submit_button('Tạo tài khoản', type='primary', use_container_width=True)
            if tao:
                ok, ket_qua = tao_tai_khoan(ten_moi, mk_moi, mk_lai)
                if ok:
                    _dang_nhap_thanh_cong(ket_qua, tao_ma_khoi_phuc(ket_qua))
                else:
                    st.error(ket_qua)
            _nut_ve_dang_nhap()
        elif man == 'quen':
            man_hinh_quen_mat_khau()
            _nut_ve_dang_nhap()
        else:
            with st.form('form_dang_nhap'):
                ten = st.text_input('Tên tài khoản', key='dn_ten', placeholder='Nhập tên tài khoản')
                mk = st.text_input('Mật khẩu', type='password', key='dn_mk', placeholder='Nhập mật khẩu')
                gui = st.form_submit_button('Đăng nhập', type='primary', use_container_width=True)
            if gui:
                con_lai = st.session_state.get('dn_khoa_den', 0) - time.time()
                if con_lai > 0:
                    st.error(f'Nhập sai quá nhiều lần. Vui lòng thử lại sau {int(con_lai) + 1} giây.')
                elif not ten.strip() or not mk:
                    st.error('Vui lòng nhập tên tài khoản và mật khẩu.')
                else:
                    ten_hien_thi = kiem_tra_dang_nhap(ten, mk)
                    if ten_hien_thi:
                        _dang_nhap_thanh_cong(ten_hien_thi)
                    else:
                        so_sai = st.session_state.get('dn_sai', 0) + 1
                        st.session_state['dn_sai'] = so_sai
                        if so_sai >= SAI_TOI_DA:
                            st.session_state['dn_khoa_den'] = time.time() + KHOA_GIAY
                            st.session_state['dn_sai'] = 0
                            st.error(f'Nhập sai {SAI_TOI_DA} lần. Đăng nhập bị tạm khóa {KHOA_GIAY} giây.')
                        else:
                            st.error('Sai tên tài khoản hoặc mật khẩu.')
            st.markdown(html_ghi_chu_dang_nhap(), unsafe_allow_html=True)
            c_tao, c_quen = st.columns(2)
            if c_tao.button('Tạo tài khoản', use_container_width=True, key='dn_vao_tao', **icon_kw('person_add')):
                _chuyen_man_dang_nhap('tao')
            if c_quen.button('Quên mật khẩu?', use_container_width=True, key='dn_vao_quen', **icon_kw('lock_reset')):
                _chuyen_man_dang_nhap('quen')

# ============ KHUNG ỨNG DỤNG: THANH TRÊN CÙNG + THANH DANH MỤC ============

CSS_KHUNG = """
<style>
@media (prefers-color-scheme: light){
  :root{ --nen:#eaf0f9; --paper:#ffffff; --bg:#e6ecf7; --line:#d3dcee; --slot:#d9e1f0; --rack-tint:#e2eafb; }
}
[data-testid="stMainBlockContainer"], .block-container{ max-width:1120px; padding-top:3.2rem; }

/* ---- thanh trên cùng ---- */
.ab{ display:flex; align-items:center; justify-content:space-between; gap:14px; padding:11px 18px; margin-bottom:20px;
  border-radius:16px; color:#fff; background:linear-gradient(100deg,#0f2263 0%,#1a3c9c 100%);
  box-shadow:0 16px 32px -20px rgba(10,25,80,.75); }
.ab-l{ display:flex; align-items:center; gap:12px; min-width:0; }
.ab-l b{ font:700 1.5rem/1 var(--f-head); letter-spacing:.3px; color:#fff; }
.ab-l span{ font:500 .95rem var(--f-ui); color:rgba(255,255,255,.80); padding-left:12px; border-left:1px solid rgba(255,255,255,.30); }
.ab-bell{ position:relative; display:grid; place-items:center; width:38px; height:38px; border-radius:12px;
  background:rgba(255,255,255,.10); border:1px solid rgba(255,255,255,.20); color:#fff; flex:none; }
.ab-bell svg{ width:19px; height:19px; }
.ab-bell i{ position:absolute; top:7px; right:8px; width:9px; height:9px; border-radius:50%; background:#ee7a14; box-shadow:0 0 0 2px #15317f; }
.ab-t{ display:flex; align-items:center; gap:12px; min-width:0; }
@media (max-width:768px){
  .ab{ background:var(--paper); color:var(--ink); border:1px solid var(--line); box-shadow:none; padding:12px 14px; border-radius:20px; }
  .ab-t{ display:block; }
  .ab-l b{ display:block; color:var(--ink); font-size:1.3rem; }
  .ab-l span{ display:block; padding-left:0; border-left:0; margin-top:3px; font-size:.72rem; color:var(--muted); }
  .ab-bell{ background:var(--bg); border-color:var(--line); color:var(--ink); }
  .ab-bell i{ box-shadow:0 0 0 2px var(--paper); }
}

/* ---- thanh danh mục bên trái ---- */
[data-testid="stSidebar"], [data-testid="stSidebar"] > div{ background:linear-gradient(185deg,#12296e 0%,#0b1d55 100%) !important; }
[data-testid="stSidebar"][aria-expanded="true"]{ min-width:236px !important; max-width:236px !important; width:236px !important; }
[data-testid="stSidebar"] [data-testid="stSidebarCollapseButton"] *, [data-testid="stSidebar"] [data-testid="stSidebarHeader"] button *{ color:rgba(255,255,255,.8) !important; }
[data-testid="stSidebar"] [data-testid="stVerticalBlock"]{ gap:.3rem; }
.nav-label{ position:relative; z-index:2; padding:16px 10px 12px; font:700 .78rem/1.4 var(--f-ui); letter-spacing:.16em;
  text-transform:uppercase; color:rgba(255,255,255,.70); }
.nav-sep{ height:1px; margin:14px 8px; background:rgba(255,255,255,.16); }
.nav-user{ display:flex; align-items:center; gap:10px; padding:6px 10px 18px; font:600 1rem var(--f-ui); color:#fff; word-break:break-all; }
.nav-user svg{ width:21px; height:21px; flex:none; }
[data-testid="stSidebar"] div[data-testid="stButton"] > button{
  justify-content:flex-start; min-height:46px; padding:0 14px; border-radius:12px;
  background:transparent; border:0; color:rgba(255,255,255,.86); box-shadow:none; }
[data-testid="stSidebar"] div[data-testid="stButton"] > button > div{ width:100%; justify-content:flex-start; gap:10px; }
[data-testid="stSidebar"] div[data-testid="stButton"] > button div[data-testid="stMarkdownContainer"]{ width:100%; }
[data-testid="stSidebar"] div[data-testid="stButton"] > button p{ text-align:left; font-size:1rem; font-weight:600; color:inherit; }
[data-testid="stSidebar"] div[data-testid="stButton"] > button [data-testid="stIconMaterial"]{ color:inherit; font-size:1.3rem; }
[data-testid="stSidebar"] div[data-testid="stButton"] > button:hover{ background:rgba(255,255,255,.09); color:#fff; border:0; }
[data-testid="stSidebar"] div[data-testid="stButton"] > button:disabled{ opacity:.4; }

/* ---- đường dẫn + tiêu đề trang ---- */
.crumb{ font:500 .85rem var(--f-ui); color:var(--muted); padding-bottom:14px; }
.crumb i{ font-style:normal; margin:0 7px; opacity:.6; }
.crumb b{ font-weight:600; color:var(--ink); }
.hd2{ display:flex; justify-content:space-between; align-items:flex-end; gap:12px; flex-wrap:wrap; margin:0 0 2px; }
.hd2-t{ margin-top:6px; font:700 clamp(1.7rem,3vw,2.2rem)/1.1 var(--f-head); color:var(--ink); }
.hd2-t .ico-img{ height:30px; width:auto; vertical-align:-6px; margin-right:10px; }
.hd2-t .ico{ width:26px; height:26px; vertical-align:-4px; margin-right:10px; }
.hd2-s{ margin-top:2px; color:var(--muted); font-size:1rem; }
.crumb + .pg-head{ margin-top:6px; }
.pg-head{ border-bottom:1px solid var(--line); }
</style>
"""

CSS_ICON_NHAP_XUAT = """
<style>
.st-key-home_nhap span[data-testid="stIconMaterial"], .st-key-home_xuat span[data-testid="stIconMaterial"]{
  font-size:0 !important; width:1.4rem; height:1.4rem; flex:none; display:inline-block;
  background-color:currentColor; -webkit-mask-repeat:no-repeat; mask-repeat:no-repeat;
  -webkit-mask-position:center; mask-position:center; -webkit-mask-size:contain; mask-size:contain; }
.st-key-home_nhap span[data-testid="stIconMaterial"]{
  -webkit-mask-image:__URI_NHAP__; mask-image:__URI_NHAP__; }
.st-key-home_xuat span[data-testid="stIconMaterial"]{
  -webkit-mask-image:__URI_XUAT__; mask-image:__URI_XUAT__; }
</style>
""".replace("__URI_NHAP__", 'url("data:image/svg+xml,%3Csvg%20xmlns=\'http://www.w3.org/2000/svg\'%20viewBox=\'0%200%2024%2024\'%20fill=\'none\'%20stroke=\'black\'%20stroke-width=\'1.9\'%20stroke-linecap=\'round\'%20stroke-linejoin=\'round\'%3E%3Cpath%20d=\'M16%2016h6\'/%3E%3Cpath%20d=\'M19%2013v6\'/%3E%3Cpath%20d=\'M21%2010V8a2%202%200%200%200-1-1.73l-7-4a2%202%200%200%200-2%200l-7%204A2%202%200%200%200%203%208v8a2%202%200%200%200%201%201.73l7%204a2%202%200%200%200%202%200l2-1.14\'/%3E%3Cpath%20d=\'m7.5%204.27%209%205.15\'/%3E%3Cpath%20d=\'M3.29%207%2012%2012l8.71-5\'/%3E%3Cpath%20d=\'M12%2022V12\'/%3E%3C/svg%3E")').replace("__URI_XUAT__", 'url("data:image/svg+xml,%3Csvg%20xmlns=\'http://www.w3.org/2000/svg\'%20viewBox=\'0%200%2024%2024\'%20fill=\'none\'%20stroke=\'black\'%20stroke-width=\'1.9\'%20stroke-linecap=\'round\'%20stroke-linejoin=\'round\'%3E%3Cpath%20d=\'M16%2016h6\'/%3E%3Cpath%20d=\'M21%2010V8a2%202%200%200%200-1-1.73l-7-4a2%202%200%200%200-2%200l-7%204A2%202%200%200%200%203%208v8a2%202%200%200%200%201%201.73l7%204a2%202%200%200%200%202%200l2-1.14\'/%3E%3Cpath%20d=\'m7.5%204.27%209%205.15\'/%3E%3Cpath%20d=\'M3.29%207%2012%2012l8.71-5\'/%3E%3Cpath%20d=\'M12%2022V12\'/%3E%3C/svg%3E")')

def _vao_tong_quan():
    st.session_state.chuc_nang = None

def _vao_ma_kp():
    st.session_state.chuc_nang = 'ma_khoi_phuc'
    st.session_state.pop('kp_trang_ma', None)

_NAV = [('tong_quan', 'Trang chủ', 'dashboard', _vao_tong_quan), ('nhap', 'Nhập hàng', 'move_to_inbox', _vao_nhap), ('xuat', 'Xuất hàng', 'outbox', _vao_xuat), ('kiem_tra', 'Kiểm tra kho', 'qr_code_scanner', _vao_kiem_tra), ('lich_su', 'Lịch sử', 'history', _vao_lich_su), ('tao_ke', 'Kệ hàng', 'shelves', _vao_tao_ke), ('tao_qr', 'Tạo mã QR', 'qr_code_2', _vao_tao_qr), ('ma_khoi_phuc', 'Mã QR khôi phục', 'key', _vao_ma_kp)]

_MUC_THEO_CHUC_NANG = {None: 'tong_quan', 'nhap': 'nhap', 'quet_nhap': 'nhap', 'xuat': 'xuat', 'quet_xuat': 'xuat', 'kiem_tra': 'kiem_tra', 'quet_kiem_tra': 'kiem_tra', 'lich_su': 'lich_su', 'tao_ke': 'tao_ke', 'tao_qr': 'tao_qr', 'ma_khoi_phuc': 'ma_khoi_phuc'}

_TEN_MUC = {k: ten for k, ten, _, _ in _NAV}

def _ti_le_su_dung():
    tong = da = 0
    for ke in st.session_state.kho.values():
        for hang in ke:
            for o in hang:
                tong += len(o)
                da += sum((1 for vt in o if vt is not None))
    return round(da * 100 / tong) if tong else 0

def thanh_nguoi_dung(ten_nguoi_dung):
    st.markdown(_gon_html(CSS_KHUNG), unsafe_allow_html=True)
    st.markdown(_gon_html(CSS_ICON_NHAP_XUAT), unsafe_allow_html=True)
    co_kho = co_ke()
    ti_le = _ti_le_su_dung() if co_kho else 0
    canh_bao = ti_le >= 90
    goi_y = f'Kho đã dùng {ti_le}% vị trí' if canh_bao else 'Không có thông báo mới'
    st.markdown(_gon_html(f'''<div class="ab"><div class="ab-l">{html_logo(38)}<div class="ab-t"><b>Stockly</b><span>Quản lý kho thông minh</span></div></div><div class="ab-bell" title="{goi_y}">{svg_tho('bell')}{('<i></i>' if canh_bao else '')}</div></div>'''), unsafe_allow_html=True)
    hien_tai = _MUC_THEO_CHUC_NANG.get(st.session_state.get('chuc_nang'), 'tong_quan')
    with st.sidebar:
        st.markdown(_gon_html(f"<style>.st-key-nav_{hien_tai} div[data-testid='stButton'] > button{{background:linear-gradient(135deg,#2a4fb8,#3d66d8) !important; color:#fff !important;box-shadow:0 10px 20px -12px rgba(0,0,0,.7) !important;}}</style>"), unsafe_allow_html=True)
        if co_kho:
            st.markdown('<div class="nav-label">Danh mục</div>', unsafe_allow_html=True)
            for ma_muc, nhan, icon, mo in _NAV:
                if st.button(nhan, key=f'nav_{ma_muc}', use_container_width=True, **icon_kw(icon)):
                    mo()
                    st.rerun()
            st.markdown('<div class="nav-sep"></div>', unsafe_allow_html=True)
        st.markdown(_gon_html(f"""<div class="nav-user">{svg_tho('user')}<span>{_esc(ten_nguoi_dung)}</span></div>"""), unsafe_allow_html=True)
        if st.button('Đăng xuất', key='dang_xuat', use_container_width=True, **icon_kw('logout')):
            huy_phien(_cookie_hien_tai() or st.session_state.get('_ma_phien'))
            st.session_state.clear()
            st.session_state['_xoa_cookie'] = True
            st.rerun()

# ============ ĐIỀU HƯỚNG CHÍNH ============

st.markdown(_gon_html(CSS_CHUNG), unsafe_allow_html=True)

nguoi_dung = st.session_state.get('nguoi_dung')

if not nguoi_dung and (not st.session_state.get('_xoa_cookie')):
    ten_khoi_phuc = tim_phien(_cookie_hien_tai())
    if ten_khoi_phuc:
        try:
            st.session_state['nguoi_dung'] = ten_khoi_phuc
            st.session_state['chuc_nang'] = None
            st.session_state['kho'] = doc_du_lieu(ten_khoi_phuc)
            st.session_state['_ma_phien'] = _cookie_hien_tai()
            nguoi_dung = ten_khoi_phuc
        except Exception:
            st.session_state.clear()
            nguoi_dung = None

if not nguoi_dung:
    if st.session_state.pop('_xoa_cookie', False):
        _js_cookie(None)
    man_hinh_dang_nhap()
    st.stop()

ma_moi = st.session_state.pop('_dat_cookie', None)
if ma_moi:
    st.session_state['_ma_phien'] = ma_moi
    _js_cookie(ma_moi)
if 'kho' not in st.session_state:
    try:
        st.session_state['kho'] = doc_du_lieu(nguoi_dung)
        st.session_state.setdefault('chuc_nang', None)
    except Exception:
        st.session_state.clear()
        st.rerun()

thanh_nguoi_dung(nguoi_dung)
hien_ma_khoi_phuc_moi()
if co_ke() and st.session_state.chuc_nang is not None:
    st.markdown(html_duong_dan(_TEN_MUC[_MUC_THEO_CHUC_NANG.get(st.session_state.chuc_nang, 'tong_quan')]), unsafe_allow_html=True)

if not co_ke():
    man_hinh_tao_ke_dau_tien()
elif st.session_state.chuc_nang is None:
    st.session_state.pop('tb_trang_chu', None)
    trang_chu()
elif st.session_state.chuc_nang == 'kiem_tra':
    man_hinh_kiem_tra()
elif st.session_state.chuc_nang == 'quet_kiem_tra':
    man_hinh_quet_kiem_tra()
elif st.session_state.chuc_nang == 'nhap':
    man_hinh_nhap()
elif st.session_state.chuc_nang == 'quet_nhap':
    man_hinh_quet_nhap()
elif st.session_state.chuc_nang == 'xuat':
    man_hinh_xuat()
elif st.session_state.chuc_nang == 'quet_xuat':
    man_hinh_quet_xuat()
elif st.session_state.chuc_nang == 'lich_su':
    man_hinh_lich_su()
elif st.session_state.chuc_nang == 'tao_qr':
    man_hinh_tao_qr()
elif st.session_state.chuc_nang == 'tao_ke':
    man_hinh_tao_ke()
elif st.session_state.chuc_nang == 'ma_khoi_phuc':
    man_hinh_ma_khoi_phuc()
