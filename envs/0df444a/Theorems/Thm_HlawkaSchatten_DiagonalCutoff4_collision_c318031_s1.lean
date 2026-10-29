-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c318031_s1
-- name    : HlawkaSchatten.DiagonalCutoff4.collision_c318031_s1
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-29T00:27:39.37767+00:00
-- url     : https://prove2.me/theorems/c571c8df-4697-43f1-a0c6-67bb9d1f53da
-- title:
--   Hlawka collision chart 318032, bounded proof step 2
-- statement:
--   For the normalized ordered chart on $[39/8,5]$ and the preceding tail-ratio bounds displayed formally, the next displayed tail-ratio bounds hold.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff4_Localization
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6 HlawkaSchatten.DiagonalCutoff4

theorem HlawkaSchatten.DiagonalCutoff4.collision_c318031_s1 (p : ℝ) (hpa : (39/8 : ℝ) ≤ p) (hpb : p ≤ (5 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (7299/4000 : ℝ) (34269/20000 : ℝ) (39911/50000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![false, true, true], ![true, true, true]])
    (hprev0 : (0 : ℝ) ≤ ((1333/2000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(1333/2000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(47383/100000 : ℝ)*X 0 1+(1 : ℝ)*X 2 0+(47383/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(7279/10000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(7279/10000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((538/3125 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(538/3125 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(299/12500 : ℝ)*X 0 1+(1 : ℝ)*X 2 0+(299/12500 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(20287/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(20287/100000 : ℝ)*X 1 2) := by sorry
