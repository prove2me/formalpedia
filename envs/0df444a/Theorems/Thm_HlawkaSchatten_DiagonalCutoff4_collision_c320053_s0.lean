-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c320053_s0
-- name    : HlawkaSchatten.DiagonalCutoff4.collision_c320053_s0
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-29T00:36:48.435008+00:00
-- url     : https://prove2.me/theorems/e81ffa6c-7e4f-4048-9b7c-7e2f67003f8c
-- title:
--   Hlawka collision chart 320054, bounded proof step 1
-- statement:
--   For the normalized ordered chart on $[5,41/8]$ and the preceding tail-ratio bounds displayed formally, the next displayed tail-ratio bounds hold.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff4_Localization
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6 HlawkaSchatten.DiagonalCutoff4

theorem HlawkaSchatten.DiagonalCutoff4.collision_c320053_s0 (p : ℝ) (hpa : (5 : ℝ) ≤ p) (hpb : p ≤ (41/8 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (4693/2500 : ℝ) (1059/625 : ℝ) (80273/100000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, false, true]]) : (0 : ℝ) ≤ ((18287/25000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(18287/25000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(4573/6250 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(4573/6250 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(4487/6250 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(4487/6250 : ℝ)*X 1 2) := by sorry
