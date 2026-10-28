-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_wide_coarse_distinct_p002_b018
-- name    : HlawkaSchatten.DiagonalCutoff4.wide_coarse_distinct_p002_b018
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-28T15:55:06.806184+00:00
-- url     : https://prove2.me/theorems/db6a5466-d220-42d5-83bc-61e0f36b39b2
-- title:
--   Hlawka reusable ordered-chart block 34–37 for 65/16 ≤ p ≤ 33/8
-- statement:
--   For p in [65/16,33/8], the displayed normalized parameters exclude each canonical chart with index c in [34,38). Indices 63 and 87, when present, are excepted.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff4_FiniteCharts
open HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem HlawkaSchatten.DiagonalCutoff4.wide_coarse_distinct_p002_b018 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (33/8 : ℝ))
    (c : Fin 88) (hlo : 34 ≤ c.val) (hhi : c.val < 38)
    (hn63 : c ≠ 63) (hn87 : c ≠ 87)
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (14917/10000 : ℝ) (36753/20000 : ℝ) (4769/6250 : ℝ) X (distinctOrders c) (distinctSigns c)) : False := by sorry
