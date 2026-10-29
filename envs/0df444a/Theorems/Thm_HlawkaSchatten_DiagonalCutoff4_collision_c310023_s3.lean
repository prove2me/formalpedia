-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c310023_s3
-- name    : HlawkaSchatten.DiagonalCutoff4.collision_c310023_s3
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-28T21:55:06.222795+00:00
-- url     : https://prove2.me/theorems/79345338-0f03-402b-b230-318c6b457292
-- title:
--   Hlawka collision chart 310024, bounded proof step 4
-- statement:
--   For the normalized ordered chart on $[35/8,9/2]$ and the preceding tail-ratio bounds displayed formally, no such real triple exists.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff4_Localization
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6 HlawkaSchatten.DiagonalCutoff4

theorem HlawkaSchatten.DiagonalCutoff4.collision_c310023_s3 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (161793/100000 : ℝ) (18111/10000 : ℝ) (2431/3125 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![false, true, false], ![true, true, true]])
    (hprev2 : (0 : ℝ) ≤ ((843/4000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(843/4000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(2711/100000 : ℝ)*X 0 1+(1 : ℝ)*X 2 0+(2711/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(6413/25000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(6413/25000 : ℝ)*X 1 2)) : False := by sorry
