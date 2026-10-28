-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c301061_s2
-- name    : HlawkaSchatten.DiagonalCutoff4.collision_c301061_s2
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-28T14:37:45.642123+00:00
-- url     : https://prove2.me/theorems/8ab5cfcc-bc4f-45c6-9d7c-8219ce0fa3ba
-- title:
--   Hlawka collision chart 301062, bounded proof step 3
-- statement:
--   For the normalized ordered chart on $[129/32,65/16]$ and the preceding tail-ratio bounds displayed formally, the next displayed tail-ratio bounds hold.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff4_Localization
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6 HlawkaSchatten.DiagonalCutoff4

theorem HlawkaSchatten.DiagonalCutoff4.collision_c301061_s2 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (36981/25000 : ℝ) (92391/50000 : ℝ) (4759/6250 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, false, true]])
    (hprev1 : (0 : ℝ) ≤ ((95537/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(95537/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(93213/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(93213/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(94361/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(94361/100000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((91913/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(91913/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(22523/25000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(22523/25000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(90637/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(90637/100000 : ℝ)*X 1 2) := by sorry
