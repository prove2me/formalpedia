-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_wide_coarse_distinct_p012_b015
-- name    : HlawkaSchatten.DiagonalCutoff4.wide_coarse_distinct_p012_b015
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-28T22:25:30.604838+00:00
-- url     : https://prove2.me/theorems/a8e03a78-6e1b-4e69-ae58-68c37bdf084f
-- title:
--   Hlawka reusable ordered-chart block 30–31 for 9/2 ≤ p ≤ 37/8
-- statement:
--   For p in [9/2,37/8], the displayed normalized parameters exclude each canonical chart with index c in [30,32). Indices 63 and 87, when present, are excepted.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff4_FiniteCharts
open HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem HlawkaSchatten.DiagonalCutoff4.wide_coarse_distinct_p012_b015 (p : ℝ) (hpa : (9/2 : ℝ) ≤ p) (hpb : p ≤ (37/8 : ℝ))
    (c : Fin 88) (hlo : 30 ≤ c.val) (hhi : c.val < 32)
    (hn63 : c ≠ 63) (hn87 : c ≠ 87)
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (166913/100000 : ℝ) (178281/100000 : ℝ) (78337/100000 : ℝ) X (distinctOrders c) (distinctSigns c)) : False := by sorry
