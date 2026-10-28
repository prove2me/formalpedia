-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c301049_s3
-- name    : HlawkaSchatten.DiagonalCutoff4.collision_c301049_s3
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-28T14:28:23.828266+00:00
-- url     : https://prove2.me/theorems/cc1c542b-61d1-4d5a-a18d-f902fb3df58d
-- title:
--   Hlawka collision chart 301050, bounded proof step 4
-- statement:
--   For the normalized ordered chart on $[129/32,65/16]$ and the preceding tail-ratio bounds displayed formally, no such real triple exists.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff4_Localization
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6 HlawkaSchatten.DiagonalCutoff4

theorem HlawkaSchatten.DiagonalCutoff4.collision_c301049_s3 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (36981/25000 : ℝ) (92391/50000 : ℝ) (4759/6250 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![false, false, true]])
    (hprev2 : (0 : ℝ) ≤ ((3057/10000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(3057/10000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(3057/10000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(3057/10000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(241/12500 : ℝ)*X 0 2+(1 : ℝ)*X 1 0+(241/12500 : ℝ)*X 1 2)) : False := by sorry
