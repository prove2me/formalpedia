-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c303083_s3
-- name    : HlawkaSchatten.DiagonalCutoff4.collision_c303083_s3
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-28T15:55:01.296264+00:00
-- url     : https://prove2.me/theorems/82a337b4-3541-4c8a-bde2-9fc2697dcfd4
-- title:
--   Hlawka collision chart 303084, bounded proof step 4
-- statement:
--   For the normalized ordered chart on $[131/32,33/8]$ and the preceding tail-ratio bounds displayed formally, no such real triple exists.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff4_Localization
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6 HlawkaSchatten.DiagonalCutoff4

theorem HlawkaSchatten.DiagonalCutoff4.collision_c303083_s3 (p : ℝ) (hpa : (131/32 : ℝ) ≤ p) (hpb : p ≤ (33/8 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (7521/5000 : ℝ) (91389/50000 : ℝ) (76461/100000 : ℝ) X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, true, true], ![true, true, true]])
    (hprev2 : (0 : ℝ) ≤ ((4661/12500 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(4661/12500 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((39379/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 0 2+(39379/100000 : ℝ)*X 2 1+(-1 : ℝ)*X 2 2) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(20629/50000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(20629/50000 : ℝ)*X 1 2)) : False := by sorry
