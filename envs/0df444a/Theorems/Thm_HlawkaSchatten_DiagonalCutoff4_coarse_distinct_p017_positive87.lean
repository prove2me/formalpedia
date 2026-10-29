-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_coarse_distinct_p017_positive87
-- name    : HlawkaSchatten.DiagonalCutoff4.coarse_distinct_p017_positive87
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-29T00:21:06.486424+00:00
-- url     : https://prove2.me/theorems/c8fa59e8-de7d-4408-876a-af435fabc0e5
-- title:
--   Hlawka positive chart 87, profile 17, has tails at most two fifths
-- statement:
--   For p in [77/16,39/8], the displayed canonical positive ordered chart has every off-main pair coordinate bounded by two fifths of its main coordinate.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff4_FiniteCharts
open HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem HlawkaSchatten.DiagonalCutoff4.coarse_distinct_p017_positive87 (p : ℝ) (hpa : (77/16 : ℝ) ≤ p) (hpb : p ≤ (39/8 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ)
    (hX : OrderedChart p (89931/50000 : ℝ) (34473/20000 : ℝ) (19897/25000 : ℝ) X (distinctOrders 87) (fun _ _ => true)) :
    ∀ j h, j ≠ h → |pair X j h| ≤ (2/5:ℝ)*pair X j j := by sorry
