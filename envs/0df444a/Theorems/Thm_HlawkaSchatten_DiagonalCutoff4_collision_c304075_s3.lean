-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c304075_s3
-- name    : HlawkaSchatten.DiagonalCutoff4.collision_c304075_s3
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-28T16:36:39.516096+00:00
-- url     : https://prove2.me/theorems/f5b91f2a-cc39-47e7-9220-6fd5ae724998
-- title:
--   Hlawka collision chart 304076, bounded proof step 4
-- statement:
--   For the normalized ordered chart on $[33/8,133/32]$ and the preceding tail-ratio bounds displayed formally, no such real triple exists.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff4_Localization
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6 HlawkaSchatten.DiagonalCutoff4

theorem HlawkaSchatten.DiagonalCutoff4.collision_c304075_s3 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (133/32 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (18959/12500 : ℝ) (187821/100000 : ℝ) (76617/100000 : ℝ) X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, false, true], ![true, false, true]])
    (hprev2 : (0 : ℝ) ≤ ((32481/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(32481/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-53227/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 0 2+(-53227/100000 : ℝ)*X 2 1+(-1 : ℝ)*X 2 2) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(37033/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(37033/100000 : ℝ)*X 1 2)) : False := by sorry
