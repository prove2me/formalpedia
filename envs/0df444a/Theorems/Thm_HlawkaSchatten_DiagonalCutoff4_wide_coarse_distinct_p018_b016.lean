-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_wide_coarse_distinct_p018_b016
-- name    : HlawkaSchatten.DiagonalCutoff4.wide_coarse_distinct_p018_b016
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-29T00:30:59.799999+00:00
-- url     : https://prove2.me/theorems/e6453415-aeac-46b6-b40b-83ae72a54884
-- title:
--   Hlawka reusable ordered-chart block 36–36 for 39/8 ≤ p ≤ 5
-- statement:
--   For p in [39/8,5], the displayed normalized parameters exclude each canonical chart with index c in [36,37). Indices 63 and 87, when present, are excepted.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff4_FiniteCharts
open HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem HlawkaSchatten.DiagonalCutoff4.wide_coarse_distinct_p018_b016 (p : ℝ) (hpa : (39/8 : ℝ) ≤ p) (hpb : p ≤ (5 : ℝ))
    (c : Fin 88) (hlo : 36 ≤ c.val) (hhi : c.val < 37)
    (hn63 : c ≠ 63) (hn87 : c ≠ 87)
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (7299/4000 : ℝ) (34269/20000 : ℝ) (39911/50000 : ℝ) X (distinctOrders c) (distinctSigns c)) : False := by sorry
