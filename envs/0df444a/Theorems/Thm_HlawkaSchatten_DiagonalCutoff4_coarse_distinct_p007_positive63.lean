-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_coarse_distinct_p007_positive63
-- name    : HlawkaSchatten.DiagonalCutoff4.coarse_distinct_p007_positive63
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-28T21:01:51.909277+00:00
-- url     : https://prove2.me/theorems/7a2091bd-f3e8-432e-8106-431dcaf3d956
-- title:
--   Hlawka positive chart 63, profile 7, has tails at most two fifths
-- statement:
--   For p in [135/32,17/4], the displayed canonical positive ordered chart has every off-main pair coordinate bounded by two fifths of its main coordinate.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff4_FiniteCharts
open HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem HlawkaSchatten.DiagonalCutoff4.coarse_distinct_p007_positive63 (p : ℝ) (hpa : (135/32 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ)
    (hX : OrderedChart p (19431/12500 : ℝ) (92559/50000 : ℝ) (4817/6250 : ℝ) X (distinctOrders 63) (fun _ _ => true)) :
    ∀ j h, j ≠ h → |pair X j h| ≤ (2/5:ℝ)*pair X j j := by sorry
