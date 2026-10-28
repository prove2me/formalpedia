-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c304050_s3
-- name    : HlawkaSchatten.DiagonalCutoff4.collision_c304050_s3
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-28T16:30:51.644374+00:00
-- url     : https://prove2.me/theorems/7854590b-f74b-4e17-b223-fa4c13f0ac64
-- title:
--   Hlawka collision chart 304051, bounded proof step 4
-- statement:
--   For the normalized ordered chart on $[33/8,17/4]$ and the preceding tail-ratio bounds displayed formally, the next displayed tail-ratio bounds hold.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff4_Localization
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6 HlawkaSchatten.DiagonalCutoff4

theorem HlawkaSchatten.DiagonalCutoff4.collision_c304050_s3 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (18959/12500 : ℝ) (187821/100000 : ℝ) (76617/100000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![false, true, false]])
    (hprev2 : (0 : ℝ) ≤ ((7919/10000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(7919/10000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(2667/4000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(2667/4000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(-54517/100000 : ℝ)*X 0 2+(1 : ℝ)*X 1 0+(-54517/100000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((52161/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(52161/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(46403/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(46403/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(-27533/100000 : ℝ)*X 0 2+(1 : ℝ)*X 1 0+(-27533/100000 : ℝ)*X 1 2) := by sorry
