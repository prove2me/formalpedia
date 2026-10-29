-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_wide_coarse_distinct_p022_b016
-- name    : HlawkaSchatten.DiagonalCutoff4.wide_coarse_distinct_p022_b016
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-29T00:44:16.311098+00:00
-- url     : https://prove2.me/theorems/7e51d0f3-4f3c-4b59-93f9-7e472678934e
-- title:
--   Hlawka reusable ordered-chart block 31–32 for 41/8 ≤ p ≤ 21/4
-- statement:
--   For p in [41/8,21/4], the displayed normalized parameters exclude each canonical chart with index c in [31,33). Indices 63 and 87, when present, are excepted.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff4_FiniteCharts
open HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem HlawkaSchatten.DiagonalCutoff4.wide_coarse_distinct_p022_b016 (p : ℝ) (hpa : (41/8 : ℝ) ≤ p) (hpb : p ≤ (21/4 : ℝ))
    (c : Fin 88) (hlo : 31 ≤ c.val) (hhi : c.val < 33)
    (hn63 : c ≠ 63) (hn87 : c ≠ 87)
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (19299/10000 : ℝ) (167697/100000 : ℝ) (2522/3125 : ℝ) X (distinctOrders c) (distinctSigns c)) : False := by sorry
