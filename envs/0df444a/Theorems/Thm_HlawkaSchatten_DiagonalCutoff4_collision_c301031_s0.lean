-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c301031_s0
-- name    : HlawkaSchatten.DiagonalCutoff4.collision_c301031_s0
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-28T14:23:23.734787+00:00
-- url     : https://prove2.me/theorems/13287799-2c01-4f85-82a3-720d779bf342
-- title:
--   Hlawka collision chart 301032, bounded proof step 1
-- statement:
--   For the normalized ordered chart on $[129/32,65/16]$ and the preceding tail-ratio bounds displayed formally, the next displayed tail-ratio bounds hold.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff4_Localization
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6 HlawkaSchatten.DiagonalCutoff4

theorem HlawkaSchatten.DiagonalCutoff4.collision_c301031_s0 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (36981/25000 : ℝ) (92391/50000 : ℝ) (4759/6250 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![false, true, true], ![true, true, true]]) : (0 : ℝ) ≤ ((83239/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(83239/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(41631/50000 : ℝ)*X 0 1+(1 : ℝ)*X 2 0+(41631/50000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(4711/5000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(4711/5000 : ℝ)*X 1 2) := by sorry
