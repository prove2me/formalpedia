-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_wide_coarse_distinct_p009_b005
-- name    : HlawkaSchatten.DiagonalCutoff4.wide_coarse_distinct_p009_b005
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-28T21:44:01.811289+00:00
-- url     : https://prove2.me/theorems/cc9a88e5-16c6-499c-a896-e97dbd5de285
-- title:
--   Hlawka reusable ordered-chart block 11–12 for 69/16 ≤ p ≤ 71/16
-- statement:
--   For p in [69/16,71/16], the displayed normalized parameters exclude each canonical chart with index c in [11,13). Indices 63 and 87, when present, are excepted.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff4_FiniteCharts
open HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem HlawkaSchatten.DiagonalCutoff4.wide_coarse_distinct_p009_b005 (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (71/16 : ℝ))
    (c : Fin 88) (hlo : 11 ≤ c.val) (hhi : c.val < 13)
    (hn63 : c ≠ 63) (hn87 : c ≠ 87)
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (159247/100000 : ℝ) (91323/50000 : ℝ) (77509/100000 : ℝ) X (distinctOrders c) (distinctSigns c)) : False := by sorry
