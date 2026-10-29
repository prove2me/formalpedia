-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c312031_s2
-- name    : HlawkaSchatten.DiagonalCutoff4.collision_c312031_s2
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-28T22:18:43.744083+00:00
-- url     : https://prove2.me/theorems/67e90ee8-96e9-4862-bc2f-5ea09b46886b
-- title:
--   Hlawka collision chart 312032, bounded proof step 3
-- statement:
--   For the normalized ordered chart on $[9/2,37/8]$ and the preceding tail-ratio bounds displayed formally, no such real triple exists.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff4_Localization
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6 HlawkaSchatten.DiagonalCutoff4

theorem HlawkaSchatten.DiagonalCutoff4.collision_c312031_s2 (p : ℝ) (hpa : (9/2 : ℝ) ≤ p) (hpb : p ≤ (37/8 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (166913/100000 : ℝ) (178281/100000 : ℝ) (78337/100000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![false, true, true], ![true, true, true]])
    (hprev1 : (0 : ℝ) ≤ ((11137/25000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(11137/25000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(2813/20000 : ℝ)*X 0 1+(1 : ℝ)*X 2 0+(2813/20000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(24841/50000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(24841/50000 : ℝ)*X 1 2)) : False := by sorry
