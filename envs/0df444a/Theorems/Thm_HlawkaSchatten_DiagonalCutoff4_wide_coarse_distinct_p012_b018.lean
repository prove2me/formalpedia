-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_wide_coarse_distinct_p012_b018
-- name    : HlawkaSchatten.DiagonalCutoff4.wide_coarse_distinct_p012_b018
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-28T22:25:43.838286+00:00
-- url     : https://prove2.me/theorems/857820c9-f7b4-4a9b-bedf-b15b42ae8f79
-- title:
--   Hlawka reusable ordered-chart block 37–37 for 9/2 ≤ p ≤ 37/8
-- statement:
--   For p in [9/2,37/8], the displayed normalized parameters exclude each canonical chart with index c in [37,38). Indices 63 and 87, when present, are excepted.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff4_FiniteCharts
open HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem HlawkaSchatten.DiagonalCutoff4.wide_coarse_distinct_p012_b018 (p : ℝ) (hpa : (9/2 : ℝ) ≤ p) (hpb : p ≤ (37/8 : ℝ))
    (c : Fin 88) (hlo : 37 ≤ c.val) (hhi : c.val < 38)
    (hn63 : c ≠ 63) (hn87 : c ≠ 87)
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (166913/100000 : ℝ) (178281/100000 : ℝ) (78337/100000 : ℝ) X (distinctOrders c) (distinctSigns c)) : False := by sorry
