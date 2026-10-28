-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c301086_s1
-- name    : HlawkaSchatten.DiagonalCutoff4.collision_c301086_s1
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-28T14:44:32.094748+00:00
-- url     : https://prove2.me/theorems/6da37b6a-2869-47ba-b5f6-bf58494f15c8
-- title:
--   Hlawka collision chart 301087, bounded proof step 2
-- statement:
--   For the normalized ordered chart on $[129/32,65/16]$ and the preceding tail-ratio bounds displayed formally, the next displayed tail-ratio bounds hold.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff4_Localization
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6 HlawkaSchatten.DiagonalCutoff4

theorem HlawkaSchatten.DiagonalCutoff4.collision_c301086_s1 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (36981/25000 : ℝ) (92391/50000 : ℝ) (4759/6250 : ℝ) X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![true, false, true], ![true, false, true]])
    (hprev0 : (0 : ℝ) ≤ ((96039/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(96039/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-97569/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 0 2+(-97569/100000 : ℝ)*X 2 1+(-1 : ℝ)*X 2 2) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(24213/25000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(24213/25000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((89341/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(89341/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-94073/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 0 2+(-94073/100000 : ℝ)*X 2 1+(-1 : ℝ)*X 2 2) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(46653/50000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(46653/50000 : ℝ)*X 1 2) := by sorry
