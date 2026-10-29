-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c317061_s3
-- name    : HlawkaSchatten.DiagonalCutoff4.collision_c317061_s3
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-29T00:22:18.011978+00:00
-- url     : https://prove2.me/theorems/8847e61a-5f0f-473f-b4c4-058810ebc99c
-- title:
--   Hlawka collision chart 317062, bounded proof step 4
-- statement:
--   For the normalized ordered chart on $[77/16,39/8]$ and the preceding tail-ratio bounds displayed formally, no such real triple exists.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff4_Localization
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6 HlawkaSchatten.DiagonalCutoff4

theorem HlawkaSchatten.DiagonalCutoff4.collision_c317061_s3 (p : ℝ) (hpa : (77/16 : ℝ) ≤ p) (hpb : p ≤ (39/8 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (89931/50000 : ℝ) (34473/20000 : ℝ) (19897/25000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, false, true]])
    (hprev2 : (0 : ℝ) ≤ ((23299/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(23299/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(181/625 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(181/625 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(13287/50000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(13287/50000 : ℝ)*X 1 2)) : False := by sorry
