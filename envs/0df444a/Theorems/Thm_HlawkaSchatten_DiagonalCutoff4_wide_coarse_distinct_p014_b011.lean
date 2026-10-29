-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_wide_coarse_distinct_p014_b011
-- name    : HlawkaSchatten.DiagonalCutoff4.wide_coarse_distinct_p014_b011
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-29T00:03:15.517854+00:00
-- url     : https://prove2.me/theorems/d4f224d5-7bb7-4a2c-ab3e-3848aab2d599
-- title:
--   Hlawka reusable ordered-chart block 22–24 for 37/8 ≤ p ≤ 19/4
-- statement:
--   For p in [37/8,19/4], the displayed normalized parameters exclude each canonical chart with index c in [22,25). Indices 63 and 87, when present, are excepted.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff4_FiniteCharts
open HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem HlawkaSchatten.DiagonalCutoff4.wide_coarse_distinct_p014_b011 (p : ℝ) (hpa : (37/8 : ℝ) ≤ p) (hpb : p ≤ (19/4 : ℝ))
    (c : Fin 88) (hlo : 22 ≤ c.val) (hhi : c.val < 25)
    (hn63 : c ≠ 63) (hn87 : c ≠ 87)
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (172069/100000 : ℝ) (87867/50000 : ℝ) (15771/20000 : ℝ) X (distinctOrders c) (distinctSigns c)) : False := by sorry
