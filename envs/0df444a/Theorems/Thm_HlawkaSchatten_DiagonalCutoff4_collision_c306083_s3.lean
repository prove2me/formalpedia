-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c306083_s3
-- name    : HlawkaSchatten.DiagonalCutoff4.collision_c306083_s3
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-28T20:41:43.09484+00:00
-- url     : https://prove2.me/theorems/f63ce722-30a3-4a0c-8b91-df8d1e491fa6
-- title:
--   Hlawka collision chart 306084, bounded proof step 4
-- statement:
--   For the normalized ordered chart on $[67/16,135/32]$ and the preceding tail-ratio bounds displayed formally, no such real triple exists.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff4_Localization
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6 HlawkaSchatten.DiagonalCutoff4

theorem HlawkaSchatten.DiagonalCutoff4.collision_c306083_s3 (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (77093/50000 : ℝ) (92997/50000 : ℝ) (38461/50000 : ℝ) X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, true, true], ![true, true, true]])
    (hprev2 : (0 : ℝ) ≤ ((36501/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(36501/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((4709/12500 : ℝ)*X 0 1+(-1 : ℝ)*X 0 2+(4709/12500 : ℝ)*X 2 1+(-1 : ℝ)*X 2 2) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(1603/4000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(1603/4000 : ℝ)*X 1 2)) : False := by sorry
