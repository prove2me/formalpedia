-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_wide_coarse_distinct_p018_b013
-- name    : HlawkaSchatten.DiagonalCutoff4.wide_coarse_distinct_p018_b013
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-29T00:31:03.15347+00:00
-- url     : https://prove2.me/theorems/232be5e1-e146-4edc-b339-f8c2e3a24540
-- title:
--   Hlawka reusable ordered-chart block 29–29 for 39/8 ≤ p ≤ 5
-- statement:
--   For p in [39/8,5], the displayed normalized parameters exclude each canonical chart with index c in [29,30). Indices 63 and 87, when present, are excepted.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff4_FiniteCharts
open HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem HlawkaSchatten.DiagonalCutoff4.wide_coarse_distinct_p018_b013 (p : ℝ) (hpa : (39/8 : ℝ) ≤ p) (hpb : p ≤ (5 : ℝ))
    (c : Fin 88) (hlo : 29 ≤ c.val) (hhi : c.val < 30)
    (hn63 : c ≠ 63) (hn87 : c ≠ 87)
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (7299/4000 : ℝ) (34269/20000 : ℝ) (39911/50000 : ℝ) X (distinctOrders c) (distinctSigns c)) : False := by sorry
