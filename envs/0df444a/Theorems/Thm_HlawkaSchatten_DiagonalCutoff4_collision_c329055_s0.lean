-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c329055_s0
-- name    : HlawkaSchatten.DiagonalCutoff4.collision_c329055_s0
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-29T01:03:36.702458+00:00
-- url     : https://prove2.me/theorems/1946e739-cedd-4b93-993c-a1b9a8f1fe7c
-- title:
--   Hlawka collision chart 329056, bounded proof step 1
-- statement:
--   For the normalized ordered chart on $[93/16,95/16]$ and the preceding tail-ratio bounds displayed formally, the next displayed tail-ratio bounds hold.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff4_Localization
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6 HlawkaSchatten.DiagonalCutoff4

theorem HlawkaSchatten.DiagonalCutoff4.collision_c329055_s0 (p : ℝ) (hpa : (93/16 : ℝ) ≤ p) (hpb : p ≤ (95/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (55589/25000 : ℝ) (160257/100000 : ℝ) (10347/12500 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, true, true]]) : (0 : ℝ) ≤ ((61467/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(61467/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(1831/3125 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(1831/3125 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(59459/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(59459/100000 : ℝ)*X 1 2) := by sorry
