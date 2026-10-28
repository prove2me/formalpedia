-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c301060_s5
-- name    : HlawkaSchatten.DiagonalCutoff4.collision_c301060_s5
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-28T14:36:57.708079+00:00
-- url     : https://prove2.me/theorems/ca7f54fc-1153-40f8-a47c-f5bd64a00dbb
-- title:
--   Hlawka collision chart 301061, bounded proof step 6
-- statement:
--   For the normalized ordered chart on $[129/32,65/16]$ and the preceding tail-ratio bounds displayed formally, the next displayed tail-ratio bounds hold.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff4_Localization
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6 HlawkaSchatten.DiagonalCutoff4

theorem HlawkaSchatten.DiagonalCutoff4.collision_c301060_s5 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (36981/25000 : ℝ) (92391/50000 : ℝ) (4759/6250 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, false, false]])
    (hprev4 : (0 : ℝ) ≤ ((75023/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(75023/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(76509/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(76509/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-64621/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-64621/100000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((6787/12500 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(6787/12500 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(58213/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(58213/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-10371/25000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-10371/25000 : ℝ)*X 1 2) := by sorry
