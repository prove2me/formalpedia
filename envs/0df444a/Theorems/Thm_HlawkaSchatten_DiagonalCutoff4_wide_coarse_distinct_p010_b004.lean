-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_wide_coarse_distinct_p010_b004
-- name    : HlawkaSchatten.DiagonalCutoff4.wide_coarse_distinct_p010_b004
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-28T22:00:48.254504+00:00
-- url     : https://prove2.me/theorems/ffa4820e-dc75-48f8-ad88-ade3ccb5418c
-- title:
--   Hlawka reusable ordered-chart block 9–10 for 35/8 ≤ p ≤ 9/2
-- statement:
--   For p in [35/8,9/2], the displayed normalized parameters exclude each canonical chart with index c in [9,11). Indices 63 and 87, when present, are excepted.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff4_FiniteCharts
open HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem HlawkaSchatten.DiagonalCutoff4.wide_coarse_distinct_p010_b004 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ))
    (c : Fin 88) (hlo : 9 ≤ c.val) (hhi : c.val < 11)
    (hn63 : c ≠ 63) (hn87 : c ≠ 87)
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (161793/100000 : ℝ) (18111/10000 : ℝ) (2431/3125 : ℝ) X (distinctOrders c) (distinctSigns c)) : False := by sorry
