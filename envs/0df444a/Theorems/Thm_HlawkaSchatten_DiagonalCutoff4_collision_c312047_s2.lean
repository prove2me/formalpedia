-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c312047_s2
-- name    : HlawkaSchatten.DiagonalCutoff4.collision_c312047_s2
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-28T22:18:58.133952+00:00
-- url     : https://prove2.me/theorems/d0f1721e-0c99-4c2d-b4a2-254af1d01e25
-- title:
--   Hlawka collision chart 312048, bounded proof step 3
-- statement:
--   For the normalized ordered chart on $[9/2,37/8]$ and the preceding tail-ratio bounds displayed formally, no such real triple exists.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff4_Localization
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6 HlawkaSchatten.DiagonalCutoff4

theorem HlawkaSchatten.DiagonalCutoff4.collision_c312047_s2 (p : ℝ) (hpa : (9/2 : ℝ) ≤ p) (hpb : p ≤ (37/8 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (166913/100000 : ℝ) (178281/100000 : ℝ) (78337/100000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, false, true], ![true, true, true]])
    (hprev1 : (0 : ℝ) ≤ ((17103/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(17103/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-17553/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(-17553/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(771/2500 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(771/2500 : ℝ)*X 1 2)) : False := by sorry
