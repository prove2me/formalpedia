-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_wide_coarse_distinct_p005_b017
-- name    : HlawkaSchatten.DiagonalCutoff4.wide_coarse_distinct_p005_b017
-- status  : Open
-- author  : @shivm
-- created : 2026-10-28T20:24:22.079961+00:00
-- url     : https://prove2.me/theorems/86a7ec68-4d9f-43e3-94dc-edb00e5f4a31
-- title:
--   Hlawka reusable ordered-chart block 32–33 for 133/32 ≤ p ≤ 137/32
-- statement:
--   For p in [133/32,137/32], the displayed normalized parameters exclude each canonical chart with index c in [32,34). Indices 63 and 87, when present, are excepted.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff4_FiniteCharts
open HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem HlawkaSchatten.DiagonalCutoff4.wide_coarse_distinct_p005_b017 (p : ℝ) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (137/32 : ℝ))
    (c : Fin 88) (hlo : 32 ≤ c.val) (hhi : c.val < 34)
    (hn63 : c ≠ 63) (hn87 : c ≠ 87)
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (4779/3125 : ℝ) (93447/50000 : ℝ) (76771/100000 : ℝ) X (distinctOrders c) (distinctSigns c)) : False := by sorry
