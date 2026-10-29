-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_wide_coarse_distinct_p016_b019
-- name    : HlawkaSchatten.DiagonalCutoff4.wide_coarse_distinct_p016_b019
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-29T00:18:24.275815+00:00
-- url     : https://prove2.me/theorems/6c4a0d71-68aa-4c47-91cf-e349a9bdf542
-- title:
--   Hlawka reusable ordered-chart block 39–40 for 19/4 ≤ p ≤ 39/8
-- statement:
--   For p in [19/4,39/8], the displayed normalized parameters exclude each canonical chart with index c in [39,41). Indices 63 and 87, when present, are excepted.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff4_FiniteCharts
open HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem HlawkaSchatten.DiagonalCutoff4.wide_coarse_distinct_p016_b019 (p : ℝ) (hpa : (19/4 : ℝ) ≤ p) (hpb : p ≤ (39/8 : ℝ))
    (c : Fin 88) (hlo : 39 ≤ c.val) (hhi : c.val < 41)
    (hn63 : c ≠ 63) (hn87 : c ≠ 87)
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (177257/100000 : ℝ) (173433/100000 : ℝ) (1587/2000 : ℝ) X (distinctOrders c) (distinctSigns c)) : False := by sorry
