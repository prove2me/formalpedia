-- Prove2me | Theorems.Thm_OddGoldbach19_table_block8000_2
-- name    : OddGoldbach19.table_block8000_2
-- status  : Proved
-- author  : @Yuxuan Xu
-- created : 2026-10-30T19:41:49.875374+00:00
-- url     : https://prove2.me/theorems/8f8ac942-68f2-446a-b71f-df67aacd2457
-- title:
--   Rounded singular-weight table certificate, block3 of5
-- statement:
--   Let $W(d)=\lceil10000\prod_{p\mid d,\ p>2}(p-1)/(p-2)\rceil$ and let $\widehat W$ be the fixed lookup table in the shared finite data. Then
--   $$W(d)\le\widehat W(d)\qquad(20000\le d<30000).$$
--   This is one of five consecutive finite comparisons covering all half-differences used by the8000-prime family.
-- source:
--   Exact finite check for the Riesel-Vaughan prime-shift method; windowed kernel-check structure adapted from public Apache2.0 accepted proof8dc0dacd-b4e9-4a76-90f1-18c613b8beee. Split into five range blocks to fit the server300-second verification limit.

import Definitions.Def_OddGoldbach19_CertificateData8000

theorem OddGoldbach19.table_block8000_2 (d : ℕ) (hlo : 20000≤d) (hhi : d<30000) :
    OddGoldbach19.Cert8000.WC d≤OddGoldbach19.Cert8000.WP d := by sorry
