-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c304039_s2
-- name    : HlawkaSchatten.DiagonalCutoff4.collision_c304039_s2
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-28T16:29:37.515291+00:00
-- url     : https://prove2.me/theorems/65f78011-7520-4a9b-9623-6fb0b0af19ee
-- title:
--   Hlawka collision chart 304040, bounded proof step 3
-- statement:
--   For the normalized ordered chart on $[33/8,17/4]$ and the preceding tail-ratio bounds displayed formally, no such real triple exists.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff4_Localization
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6 HlawkaSchatten.DiagonalCutoff4

theorem HlawkaSchatten.DiagonalCutoff4.collision_c304039_s2 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (18959/12500 : ℝ) (187821/100000 : ℝ) (76617/100000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, false, false], ![true, true, true]])
    (hprev1 : (0 : ℝ) ≤ ((9377/20000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(9377/20000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-5179/12500 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(-5179/12500 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(13739/20000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(13739/20000 : ℝ)*X 1 2)) : False := by sorry
