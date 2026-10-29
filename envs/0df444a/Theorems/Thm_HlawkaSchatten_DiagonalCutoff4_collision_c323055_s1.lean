-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c323055_s1
-- name    : HlawkaSchatten.DiagonalCutoff4.collision_c323055_s1
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-29T00:46:04.530995+00:00
-- url     : https://prove2.me/theorems/58de214d-4455-40b3-a601-c3f7a4aa9c6b
-- title:
--   Hlawka collision chart 323056, bounded proof step 2
-- statement:
--   For the normalized ordered chart on $[83/16,21/4]$ and the preceding tail-ratio bounds displayed formally, the next displayed tail-ratio bounds hold.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff4_Localization
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6 HlawkaSchatten.DiagonalCutoff4

theorem HlawkaSchatten.DiagonalCutoff4.collision_c323055_s1 (p : ℝ) (hpa : (83/16 : ℝ) ≤ p) (hpb : p ≤ (21/4 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (97817/50000 : ℝ) (166881/100000 : ℝ) (80913/100000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, true, true]])
    (hprev0 : (0 : ℝ) ≤ ((35183/50000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(35183/50000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(67167/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(67167/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(68361/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(68361/100000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((39823/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(39823/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(40323/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(40323/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(40201/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(40201/100000 : ℝ)*X 1 2) := by sorry
