-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_coarse_distinct_p022_positive87
-- name    : HlawkaSchatten.DiagonalCutoff4.coarse_distinct_p022_positive87
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-29T00:42:30.53539+00:00
-- url     : https://prove2.me/theorems/a14c2893-a2d0-4d5d-a348-73e160aab079
-- title:
--   Hlawka positive chart 87, profile 22, has tails at most two fifths
-- statement:
--   For p in [41/8,83/16], the displayed canonical positive ordered chart has every off-main pair coordinate bounded by two fifths of its main coordinate.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff4_FiniteCharts
open HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem HlawkaSchatten.DiagonalCutoff4.coarse_distinct_p022_positive87 (p : ℝ) (hpa : (41/8 : ℝ) ≤ p) (hpb : p ≤ (83/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ)
    (hX : OrderedChart p (19299/10000 : ℝ) (167697/100000 : ℝ) (2522/3125 : ℝ) X (distinctOrders 87) (fun _ _ => true)) :
    ∀ j h, j ≠ h → |pair X j h| ≤ (2/5:ℝ)*pair X j j := by sorry
