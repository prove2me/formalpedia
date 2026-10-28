-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c10083_s4
-- name    : HlawkaSchatten.DiagonalCutoff4.collision_c10083_s4
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-28T12:37:28.111036+00:00
-- url     : https://prove2.me/theorems/7b70082b-f5ce-4c88-9d07-2d5a720446ff
-- title:
--   Hlawka collision chart 10084, bounded proof step 5
-- statement:
--   For the normalized ordered chart on $[4,129/32]$ and the preceding tail-ratio bounds displayed formally, no such real triple exists.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff4_Localization
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6 HlawkaSchatten.DiagonalCutoff4

theorem HlawkaSchatten.DiagonalCutoff4.collision_c10083_s4 (p : ℝ) (hpa : (4 : ℝ) ≤ p) (hpb : p ≤ (129/32 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (3667/2500 : ℝ) (37167/20000 : ℝ) (37991/50000 : ℝ) X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, true, true], ![true, true, true]])
    (hprev3 : (0 : ℝ) ≤ ((3321/12500 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(3321/12500 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((6091/20000 : ℝ)*X 0 1+(-1 : ℝ)*X 0 2+(6091/20000 : ℝ)*X 2 1+(-1 : ℝ)*X 2 2) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(239/800 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(239/800 : ℝ)*X 1 2)) : False := by sorry
