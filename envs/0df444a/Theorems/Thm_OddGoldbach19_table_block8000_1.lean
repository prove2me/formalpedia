-- Prove2me | Theorems.Thm_OddGoldbach19_table_block8000_1
-- name    : OddGoldbach19.table_block8000_1
-- status  : Proved
-- author  : @Yuxuan Xu
-- created : 2026-10-30T19:41:47.070997+00:00
-- url     : https://prove2.me/theorems/bcd803b0-f94c-43c9-90aa-e291acac29a7
-- title:
--   Rounded singular-weight table certificate, block2 of5
-- statement:
--   Let $W(d)=\lceil10000\prod_{p\mid d,\ p>2}(p-1)/(p-2)\rceil$ and let $\widehat W$ be the fixed lookup table in the shared finite data. Then
--   $$W(d)\le\widehat W(d)\qquad(10000\le d<20000).$$
--   This is one of five consecutive finite comparisons covering all half-differences used by the8000-prime family.
-- source:
--   Exact finite check for the Riesel-Vaughan prime-shift method; windowed kernel-check structure adapted from public Apache2.0 accepted proof8dc0dacd-b4e9-4a76-90f1-18c613b8beee. Split into five range blocks to fit the server300-second verification limit.

import Definitions.Def_OddGoldbach19_CertificateData8000

theorem OddGoldbach19.table_block8000_1 (d : ℕ) (hlo : 10000≤d) (hhi : d<20000) :
    OddGoldbach19.Cert8000.WC d≤OddGoldbach19.Cert8000.WP d := by sorry
