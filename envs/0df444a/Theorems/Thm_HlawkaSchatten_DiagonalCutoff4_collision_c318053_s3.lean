-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c318053_s3
-- name    : HlawkaSchatten.DiagonalCutoff4.collision_c318053_s3
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-29T00:28:00.680222+00:00
-- url     : https://prove2.me/theorems/68a005b8-a177-4108-a383-cb1c3d889f98
-- title:
--   Hlawka collision chart 318054, bounded proof step 4
-- statement:
--   For the normalized ordered chart on $[39/8,5]$ and the preceding tail-ratio bounds displayed formally, no such real triple exists.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff4_Localization
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6 HlawkaSchatten.DiagonalCutoff4

theorem HlawkaSchatten.DiagonalCutoff4.collision_c318053_s3 (p : ℝ) (hpa : (39/8 : ℝ) ≤ p) (hpb : p ≤ (5 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (7299/4000 : ℝ) (34269/20000 : ℝ) (39911/50000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, false, true]])
    (hprev2 : (0 : ℝ) ≤ ((11839/50000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(11839/50000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(14361/50000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(14361/50000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(13847/50000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(13847/50000 : ℝ)*X 1 2)) : False := by sorry
