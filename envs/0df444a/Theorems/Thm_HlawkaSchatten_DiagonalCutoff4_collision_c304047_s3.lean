-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c304047_s3
-- name    : HlawkaSchatten.DiagonalCutoff4.collision_c304047_s3
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-28T16:29:49.200542+00:00
-- url     : https://prove2.me/theorems/47491d56-1cf5-44a6-a9bf-b5390287ab78
-- title:
--   Hlawka collision chart 304048, bounded proof step 4
-- statement:
--   For the normalized ordered chart on $[33/8,17/4]$ and the preceding tail-ratio bounds displayed formally, no such real triple exists.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff4_Localization
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6 HlawkaSchatten.DiagonalCutoff4

theorem HlawkaSchatten.DiagonalCutoff4.collision_c304047_s3 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (18959/12500 : ℝ) (187821/100000 : ℝ) (76617/100000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, false, true], ![true, true, true]])
    (hprev2 : (0 : ℝ) ≤ ((5813/25000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(5813/25000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-5451/25000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(-5451/25000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(38387/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(38387/100000 : ℝ)*X 1 2)) : False := by sorry
