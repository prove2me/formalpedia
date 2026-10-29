-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_wide_coarse_distinct_p012_b000
-- name    : HlawkaSchatten.DiagonalCutoff4.wide_coarse_distinct_p012_b000
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-28T22:25:03.32585+00:00
-- url     : https://prove2.me/theorems/91f88748-dbbd-4514-94d6-a9821ce71885
-- title:
--   Hlawka reusable ordered-chart block 0–2 for 9/2 ≤ p ≤ 37/8
-- statement:
--   For p in [9/2,37/8], the displayed normalized parameters exclude each canonical chart with index c in [0,3). Indices 63 and 87, when present, are excepted.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff4_FiniteCharts
open HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem HlawkaSchatten.DiagonalCutoff4.wide_coarse_distinct_p012_b000 (p : ℝ) (hpa : (9/2 : ℝ) ≤ p) (hpb : p ≤ (37/8 : ℝ))
    (c : Fin 88) (hlo : 0 ≤ c.val) (hhi : c.val < 3)
    (hn63 : c ≠ 63) (hn87 : c ≠ 87)
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (166913/100000 : ℝ) (178281/100000 : ℝ) (78337/100000 : ℝ) X (distinctOrders c) (distinctSigns c)) : False := by sorry
