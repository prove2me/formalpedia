-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_wide_coarse_distinct_p023_b022
-- name    : HlawkaSchatten.DiagonalCutoff4.wide_coarse_distinct_p023_b022
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-29T00:46:40.995472+00:00
-- url     : https://prove2.me/theorems/d909b4b6-59c1-434c-9a5f-bce60bf0b45e
-- title:
--   Hlawka reusable ordered-chart block 41–43 for 83/16 ≤ p ≤ 85/16
-- statement:
--   For p in [83/16,85/16], the displayed normalized parameters exclude each canonical chart with index c in [41,44). Indices 63 and 87, when present, are excepted.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff4_FiniteCharts
open HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem HlawkaSchatten.DiagonalCutoff4.wide_coarse_distinct_p023_b022 (p : ℝ) (hpa : (83/16 : ℝ) ≤ p) (hpb : p ≤ (85/16 : ℝ))
    (c : Fin 88) (hlo : 41 ≤ c.val) (hhi : c.val < 44)
    (hn63 : c ≠ 63) (hn87 : c ≠ 87)
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (97817/50000 : ℝ) (166881/100000 : ℝ) (80913/100000 : ℝ) X (distinctOrders c) (distinctSigns c)) : False := by sorry
