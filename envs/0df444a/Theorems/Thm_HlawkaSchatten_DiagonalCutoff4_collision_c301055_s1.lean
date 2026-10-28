-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c301055_s1
-- name    : HlawkaSchatten.DiagonalCutoff4.collision_c301055_s1
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-28T14:31:54.443002+00:00
-- url     : https://prove2.me/theorems/b8e6b348-1363-4ff0-a87f-c6a82b24d0e8
-- title:
--   Hlawka collision chart 301056, bounded proof step 2
-- statement:
--   For the normalized ordered chart on $[129/32,65/16]$ and the preceding tail-ratio bounds displayed formally, the next displayed tail-ratio bounds hold.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff4_Localization
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6 HlawkaSchatten.DiagonalCutoff4

theorem HlawkaSchatten.DiagonalCutoff4.collision_c301055_s1 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (36981/25000 : ℝ) (92391/50000 : ℝ) (4759/6250 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, true, true]])
    (hprev0 : (0 : ℝ) ≤ ((48511/50000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(48511/50000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(9769/10000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(9769/10000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(19179/20000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(19179/20000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((94029/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(94029/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(94431/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(94431/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(23043/25000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(23043/25000 : ℝ)*X 1 2) := by sorry
