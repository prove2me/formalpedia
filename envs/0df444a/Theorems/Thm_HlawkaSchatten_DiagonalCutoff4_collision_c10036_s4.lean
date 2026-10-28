-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c10036_s4
-- name    : HlawkaSchatten.DiagonalCutoff4.collision_c10036_s4
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-28T12:14:13.617538+00:00
-- url     : https://prove2.me/theorems/c4b50a5c-4cbb-4a56-bfd6-785579681aee
-- title:
--   Hlawka collision chart 10037, bounded proof step 5
-- statement:
--   For the normalized ordered chart on $[4,33/8]$ and the preceding tail-ratio bounds displayed formally, no such real triple exists.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff4_Localization
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6 HlawkaSchatten.DiagonalCutoff4

theorem HlawkaSchatten.DiagonalCutoff4.collision_c10036_s4 (p : ℝ) (hpa : (4 : ℝ) ≤ p) (hpb : p ≤ (33/8 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (3667/2500 : ℝ) (37167/20000 : ℝ) (37991/50000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, false, false], ![true, false, false]])
    (hprev3 : (0 : ℝ) ≤ ((4907/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(4907/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-23179/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(-23179/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-23191/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-23191/100000 : ℝ)*X 1 2)) : False := by sorry
