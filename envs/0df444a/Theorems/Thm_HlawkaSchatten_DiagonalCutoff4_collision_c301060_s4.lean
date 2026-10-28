-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c301060_s4
-- name    : HlawkaSchatten.DiagonalCutoff4.collision_c301060_s4
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-28T14:36:39.584042+00:00
-- url     : https://prove2.me/theorems/5b7f704e-a986-48dd-9f25-b8eee55a1102
-- title:
--   Hlawka collision chart 301061, bounded proof step 5
-- statement:
--   For the normalized ordered chart on $[129/32,65/16]$ and the preceding tail-ratio bounds displayed formally, the next displayed tail-ratio bounds hold.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff4_Localization
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6 HlawkaSchatten.DiagonalCutoff4

theorem HlawkaSchatten.DiagonalCutoff4.collision_c301060_s4 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (36981/25000 : ℝ) (92391/50000 : ℝ) (4759/6250 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, false, false]])
    (hprev3 : (0 : ℝ) ≤ ((42263/50000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(42263/50000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(42719/50000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(42719/50000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-75997/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-75997/100000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((75023/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(75023/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(76509/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(76509/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-64621/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-64621/100000 : ℝ)*X 1 2) := by sorry
