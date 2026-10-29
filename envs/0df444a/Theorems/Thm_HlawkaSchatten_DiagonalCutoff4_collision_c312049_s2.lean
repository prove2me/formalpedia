-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c312049_s2
-- name    : HlawkaSchatten.DiagonalCutoff4.collision_c312049_s2
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-28T22:19:03.463276+00:00
-- url     : https://prove2.me/theorems/fef6ed3f-280b-4375-bdf5-eaf629e41c59
-- title:
--   Hlawka collision chart 312050, bounded proof step 3
-- statement:
--   For the normalized ordered chart on $[9/2,37/8]$ and the preceding tail-ratio bounds displayed formally, no such real triple exists.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff4_Localization
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6 HlawkaSchatten.DiagonalCutoff4

theorem HlawkaSchatten.DiagonalCutoff4.collision_c312049_s2 (p : ℝ) (hpa : (9/2 : ℝ) ≤ p) (hpb : p ≤ (37/8 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (166913/100000 : ℝ) (178281/100000 : ℝ) (78337/100000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![false, false, true]])
    (hprev1 : (0 : ℝ) ≤ ((21671/50000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(21671/50000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(43343/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(43343/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(591/12500 : ℝ)*X 0 2+(1 : ℝ)*X 1 0+(591/12500 : ℝ)*X 1 2)) : False := by sorry
