-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c314051_s2
-- name    : HlawkaSchatten.DiagonalCutoff4.collision_c314051_s2
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-29T00:00:00.310987+00:00
-- url     : https://prove2.me/theorems/b6159fc2-4766-4967-913c-52e5fd6e9d57
-- title:
--   Hlawka collision chart 314052, bounded proof step 3
-- statement:
--   For the normalized ordered chart on $[37/8,19/4]$ and the preceding tail-ratio bounds displayed formally, no such real triple exists.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff4_Localization
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6 HlawkaSchatten.DiagonalCutoff4

theorem HlawkaSchatten.DiagonalCutoff4.collision_c314051_s2 (p : ℝ) (hpa : (37/8 : ℝ) ≤ p) (hpb : p ≤ (19/4 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (172069/100000 : ℝ) (87867/50000 : ℝ) (15771/20000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![false, true, true]])
    (hprev1 : (0 : ℝ) ≤ ((36337/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(36337/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(2267/6250 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(2267/6250 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(6161/100000 : ℝ)*X 0 2+(1 : ℝ)*X 1 0+(6161/100000 : ℝ)*X 1 2)) : False := by sorry
