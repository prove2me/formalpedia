-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c308080_s3
-- name    : HlawkaSchatten.DiagonalCutoff4.collision_c308080_s3
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-28T21:25:39.853083+00:00
-- url     : https://prove2.me/theorems/15c35163-5589-4328-bed5-a8b1f085792f
-- title:
--   Hlawka collision chart 308081, bounded proof step 4
-- statement:
--   For the normalized ordered chart on $[17/4,69/16]$ and the preceding tail-ratio bounds displayed formally, no such real triple exists.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff4_Localization
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6 HlawkaSchatten.DiagonalCutoff4

theorem HlawkaSchatten.DiagonalCutoff4.collision_c308080_s3 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (69/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (156711/100000 : ℝ) (11517/6250 : ℝ) (3861/5000 : ℝ) X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, true, false], ![true, true, true]])
    (hprev2 : (0 : ℝ) ≤ ((30261/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(30261/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((3323/50000 : ℝ)*X 0 1+(1 : ℝ)*X 0 2+(3323/50000 : ℝ)*X 2 1+(1 : ℝ)*X 2 2) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(36247/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(36247/100000 : ℝ)*X 1 2)) : False := by sorry
