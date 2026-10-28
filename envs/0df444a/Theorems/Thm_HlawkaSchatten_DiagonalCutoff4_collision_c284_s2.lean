-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c284_s2
-- name    : HlawkaSchatten.DiagonalCutoff4.collision_c284_s2
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-28T11:40:56.475192+00:00
-- url     : https://prove2.me/theorems/2ab956f4-d2af-4e66-8f52-27c588affe48
-- title:
--   Hlawka collision chart 285, bounded proof step 3
-- statement:
--   For the normalized ordered chart on $[4,33/8]$ and the preceding tail-ratio bounds displayed formally, no such real triple exists.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff4_Localization
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6 HlawkaSchatten.DiagonalCutoff4

theorem HlawkaSchatten.DiagonalCutoff4.collision_c284_s2 (p : ℝ) (hpa : (4 : ℝ) ≤ p) (hpb : p ≤ (33/8 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (3667/2500 : ℝ) (37167/20000 : ℝ) (37991/50000 : ℝ) X ![![0, 2, 1], ![0, 2, 1], ![1, 0, 2]] ![![true, true, true], ![true, true, true], ![true, false, true]])
    (hprev0 : (0 : ℝ) ≤ ((99391/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 2+(99391/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 2) ∧ (0 : ℝ) ≤ ((99391/100000 : ℝ)*X 0 0+(-1 : ℝ)*X 0 2+(99391/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 2) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-13631/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 1 0+(-13631/100000 : ℝ)*X 1 1))
    (hprev1 : (0 : ℝ) ≤ ((87233/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 2+(87233/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 2) ∧ (0 : ℝ) ≤ ((87233/100000 : ℝ)*X 0 0+(-1 : ℝ)*X 0 2+(87233/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 2) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-219/2000 : ℝ)*X 0 1+(-1 : ℝ)*X 1 0+(-219/2000 : ℝ)*X 1 1)) : False := by sorry
