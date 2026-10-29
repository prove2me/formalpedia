-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_wide_coarse_distinct_p020_b008
-- name    : HlawkaSchatten.DiagonalCutoff4.wide_coarse_distinct_p020_b008
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-29T00:38:08.185521+00:00
-- url     : https://prove2.me/theorems/7f044a55-5838-4962-ac98-3527c9fa753b
-- title:
--   Hlawka reusable ordered-chart block 19–20 for 5 ≤ p ≤ 41/8
-- statement:
--   For p in [5,41/8], the displayed normalized parameters exclude each canonical chart with index c in [19,21). Indices 63 and 87, when present, are excepted.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff4_FiniteCharts
open HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem HlawkaSchatten.DiagonalCutoff4.wide_coarse_distinct_p020_b008 (p : ℝ) (hpa : (5 : ℝ) ≤ p) (hpb : p ≤ (41/8 : ℝ))
    (c : Fin 88) (hlo : 19 ≤ c.val) (hhi : c.val < 21)
    (hn63 : c ≠ 63) (hn87 : c ≠ 87)
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (4693/2500 : ℝ) (1059/625 : ℝ) (80273/100000 : ℝ) X (distinctOrders c) (distinctSigns c)) : False := by sorry
