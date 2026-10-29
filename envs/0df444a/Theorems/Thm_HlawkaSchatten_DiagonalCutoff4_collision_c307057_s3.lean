-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c307057_s3
-- name    : HlawkaSchatten.DiagonalCutoff4.collision_c307057_s3
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-28T21:02:06.026201+00:00
-- url     : https://prove2.me/theorems/1f339e16-7bb8-42d8-9846-d81bc39db6ea
-- title:
--   Hlawka collision chart 307058, bounded proof step 4
-- statement:
--   For the normalized ordered chart on $[135/32,17/4]$ and the preceding tail-ratio bounds displayed formally, the next displayed tail-ratio bounds hold.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff4_Localization
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6 HlawkaSchatten.DiagonalCutoff4

theorem HlawkaSchatten.DiagonalCutoff4.collision_c307057_s3 (p : ℝ) (hpa : (135/32 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (19431/12500 : ℝ) (92559/50000 : ℝ) (4817/6250 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![false, false, true]])
    (hprev2 : (0 : ℝ) ≤ ((69361/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(69361/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(69331/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(69331/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(3021/20000 : ℝ)*X 0 2+(1 : ℝ)*X 1 0+(3021/20000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((4623/12500 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(4623/12500 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(36981/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(36981/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(4913/100000 : ℝ)*X 0 2+(1 : ℝ)*X 1 0+(4913/100000 : ℝ)*X 1 2) := by sorry
