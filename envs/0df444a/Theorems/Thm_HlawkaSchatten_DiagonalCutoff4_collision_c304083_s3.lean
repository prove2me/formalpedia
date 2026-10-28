-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c304083_s3
-- name    : HlawkaSchatten.DiagonalCutoff4.collision_c304083_s3
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-28T16:37:15.264429+00:00
-- url     : https://prove2.me/theorems/d05a16d1-7633-4f57-8af2-b4b4e30c1c57
-- title:
--   Hlawka collision chart 304084, bounded proof step 4
-- statement:
--   For the normalized ordered chart on $[33/8,133/32]$ and the preceding tail-ratio bounds displayed formally, the next displayed tail-ratio bounds hold.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff4_Localization
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6 HlawkaSchatten.DiagonalCutoff4

theorem HlawkaSchatten.DiagonalCutoff4.collision_c304083_s3 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (133/32 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (18959/12500 : ℝ) (187821/100000 : ℝ) (76617/100000 : ℝ) X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, true, true], ![true, true, true]])
    (hprev2 : (0 : ℝ) ≤ ((47801/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(47801/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((5631/12500 : ℝ)*X 0 1+(-1 : ℝ)*X 0 2+(5631/12500 : ℝ)*X 2 1+(-1 : ℝ)*X 2 2) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(10493/20000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(10493/20000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((1179/6250 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(1179/6250 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((21823/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 0 2+(21823/100000 : ℝ)*X 2 1+(-1 : ℝ)*X 2 2) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(20683/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(20683/100000 : ℝ)*X 1 2) := by sorry
