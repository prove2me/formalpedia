-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c320052_s0
-- name    : HlawkaSchatten.DiagonalCutoff4.collision_c320052_s0
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-29T00:36:47.064999+00:00
-- url     : https://prove2.me/theorems/747b29c9-d3e2-4b03-93b3-73434e81ccce
-- title:
--   Hlawka collision chart 320053, bounded proof step 1
-- statement:
--   For the normalized ordered chart on $[5,41/8]$ and the preceding tail-ratio bounds displayed formally, the next displayed tail-ratio bounds hold.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff4_Localization
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6 HlawkaSchatten.DiagonalCutoff4

theorem HlawkaSchatten.DiagonalCutoff4.collision_c320052_s0 (p : ℝ) (hpa : (5 : ℝ) ≤ p) (hpb : p ≤ (41/8 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (4693/2500 : ℝ) (1059/625 : ℝ) (80273/100000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, false, false]]) : (0 : ℝ) ≤ ((68317/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(68317/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(13859/20000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(13859/20000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-5741/10000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-5741/10000 : ℝ)*X 1 2) := by sorry
