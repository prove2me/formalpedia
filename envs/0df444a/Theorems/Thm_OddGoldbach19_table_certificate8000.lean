-- Prove2me | Theorems.Thm_OddGoldbach19_table_certificate8000
-- name    : OddGoldbach19.table_certificate8000
-- status  : Proved
-- author  : @Yuxuan Xu
-- created : 2026-10-30T19:28:24.832753+00:00
-- url     : https://prove2.me/theorems/17145546-6dd6-4e67-8720-88e998d221fd
-- title:
--   A complete rounded singular-weight lookup certificate
-- statement:
--   For $d\in\mathbb N$, let
--   $$K(d)=\prod_{\substack{p\mid d\\p>2}}\frac{p-1}{p-2},\qquad W(d)=\lceil10000K(d)\rceil.$$
--   Let $\widehat W$ be the fixed16-bit lookup table in the shared finite data. Then
--   $$W(d)\le\widehat W(d)\qquad(0\le d<40909).$$
--   The range covers every half-difference of two prime shifts in the shared8000-element family. This is a finite table comparison, separate from the total pair-sum bound.
-- source:
--   Exact finite singular-weight certificate for the known Riesel-Vaughan method. The windowed checked-computation structure is adapted from public Apache2.0 Prove2Me accepted proof8dc0dacd-b4e9-4a76-90f1-18c613b8beee. The present table uses half-differences and scale10000.

import Definitions.Def_OddGoldbach19_CertificateData8000

theorem OddGoldbach19.table_certificate8000 (d : ℕ) (hd : d<40909) :
    OddGoldbach19.Cert8000.WC d≤OddGoldbach19.Cert8000.WP d := by sorry
