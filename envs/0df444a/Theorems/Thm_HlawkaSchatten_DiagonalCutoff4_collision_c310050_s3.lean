-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c310050_s3
-- name    : HlawkaSchatten.DiagonalCutoff4.collision_c310050_s3
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-28T21:56:29.358604+00:00
-- url     : https://prove2.me/theorems/9180d526-052f-47f3-9b46-1dd074cc6225
-- title:
--   Hlawka collision chart 310051, bounded proof step 4
-- statement:
--   For the normalized ordered chart on $[35/8,9/2]$ and the preceding tail-ratio bounds displayed formally, no such real triple exists.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff4_Localization
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6 HlawkaSchatten.DiagonalCutoff4

theorem HlawkaSchatten.DiagonalCutoff4.collision_c310050_s3 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (161793/100000 : ℝ) (18111/10000 : ℝ) (2431/3125 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![false, true, false]])
    (hprev2 : (0 : ℝ) ≤ ((8879/25000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(8879/25000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(1009/3125 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(1009/3125 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(-7461/50000 : ℝ)*X 0 2+(1 : ℝ)*X 1 0+(-7461/50000 : ℝ)*X 1 2)) : False := by sorry
