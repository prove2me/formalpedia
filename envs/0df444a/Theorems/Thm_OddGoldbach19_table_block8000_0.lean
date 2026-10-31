-- Prove2me | Theorems.Thm_OddGoldbach19_table_block8000_0
-- name    : OddGoldbach19.table_block8000_0
-- status  : Proved
-- author  : @Yuxuan Xu
-- created : 2026-10-30T19:41:48.019964+00:00
-- url     : https://prove2.me/theorems/32ea1442-bf81-48a3-92b9-94262ad5e95a
-- title:
--   Rounded singular-weight table certificate, block1 of5
-- statement:
--   Let $W(d)=\lceil10000\prod_{p\mid d,\ p>2}(p-1)/(p-2)\rceil$ and let $\widehat W$ be the fixed lookup table in the shared finite data. Then
--   $$W(d)\le\widehat W(d)\qquad(0\le d<10000).$$
--   This is one of five consecutive finite comparisons covering all half-differences used by the8000-prime family.
-- source:
--   Exact finite check for the Riesel-Vaughan prime-shift method; windowed kernel-check structure adapted from public Apache2.0 accepted proof8dc0dacd-b4e9-4a76-90f1-18c613b8beee. Split into five range blocks to fit the server300-second verification limit.

import Definitions.Def_OddGoldbach19_CertificateData8000

theorem OddGoldbach19.table_block8000_0 (d : ℕ) (hlo : 0≤d) (hhi : d<10000) :
    OddGoldbach19.Cert8000.WC d≤OddGoldbach19.Cert8000.WP d := by sorry
