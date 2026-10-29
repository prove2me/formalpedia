-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_wide_coarse_distinct_p020_b013
-- name    : HlawkaSchatten.DiagonalCutoff4.wide_coarse_distinct_p020_b013
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-29T00:38:16.776122+00:00
-- url     : https://prove2.me/theorems/f70d32b3-40fa-43c1-8c1b-cd0649a07bfc
-- title:
--   Hlawka reusable ordered-chart block 27–28 for 5 ≤ p ≤ 41/8
-- statement:
--   For p in [5,41/8], the displayed normalized parameters exclude each canonical chart with index c in [27,29). Indices 63 and 87, when present, are excepted.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff4_FiniteCharts
open HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem HlawkaSchatten.DiagonalCutoff4.wide_coarse_distinct_p020_b013 (p : ℝ) (hpa : (5 : ℝ) ≤ p) (hpb : p ≤ (41/8 : ℝ))
    (c : Fin 88) (hlo : 27 ≤ c.val) (hhi : c.val < 29)
    (hn63 : c ≠ 63) (hn87 : c ≠ 87)
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (4693/2500 : ℝ) (1059/625 : ℝ) (80273/100000 : ℝ) X (distinctOrders c) (distinctSigns c)) : False := by sorry
