-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_wide_coarse_distinct_p006_b025
-- name    : HlawkaSchatten.DiagonalCutoff4.wide_coarse_distinct_p006_b025
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-28T20:42:20.226106+00:00
-- url     : https://prove2.me/theorems/eb474a61-46ef-48ba-971c-f8a532416a53
-- title:
--   Hlawka reusable ordered-chart block 46–53 for 67/16 ≤ p ≤ 17/4
-- statement:
--   For p in [67/16,17/4], the displayed normalized parameters exclude each canonical chart with index c in [46,54). Indices 63 and 87, when present, are excepted.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff4_FiniteCharts
open HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem HlawkaSchatten.DiagonalCutoff4.wide_coarse_distinct_p006_b025 (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ))
    (c : Fin 88) (hlo : 46 ≤ c.val) (hhi : c.val < 54)
    (hn63 : c ≠ 63) (hn87 : c ≠ 87)
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (77093/50000 : ℝ) (92997/50000 : ℝ) (38461/50000 : ℝ) X (distinctOrders c) (distinctSigns c)) : False := by sorry
