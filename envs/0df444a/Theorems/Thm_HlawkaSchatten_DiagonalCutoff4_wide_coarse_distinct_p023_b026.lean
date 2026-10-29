-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_wide_coarse_distinct_p023_b026
-- name    : HlawkaSchatten.DiagonalCutoff4.wide_coarse_distinct_p023_b026
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-29T00:47:13.946516+00:00
-- url     : https://prove2.me/theorems/6299e843-35b8-400f-b089-3180b22a95c0
-- title:
--   Hlawka reusable ordered-chart block 48–48 for 83/16 ≤ p ≤ 85/16
-- statement:
--   For p in [83/16,85/16], the displayed normalized parameters exclude each canonical chart with index c in [48,49). Indices 63 and 87, when present, are excepted.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff4_FiniteCharts
open HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem HlawkaSchatten.DiagonalCutoff4.wide_coarse_distinct_p023_b026 (p : ℝ) (hpa : (83/16 : ℝ) ≤ p) (hpb : p ≤ (85/16 : ℝ))
    (c : Fin 88) (hlo : 48 ≤ c.val) (hhi : c.val < 49)
    (hn63 : c ≠ 63) (hn87 : c ≠ 87)
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (97817/50000 : ℝ) (166881/100000 : ℝ) (80913/100000 : ℝ) X (distinctOrders c) (distinctSigns c)) : False := by sorry
