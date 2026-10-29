-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c327055_s2
-- name    : HlawkaSchatten.DiagonalCutoff4.collision_c327055_s2
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-29T00:58:44.821849+00:00
-- url     : https://prove2.me/theorems/9865f838-51f3-4083-ba51-83c2ecdfa28c
-- title:
--   Hlawka collision chart 327056, bounded proof step 3
-- statement:
--   For the normalized ordered chart on $[89/16,91/16]$ and the preceding tail-ratio bounds displayed formally, no such real triple exists.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff4_Localization
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6 HlawkaSchatten.DiagonalCutoff4

theorem HlawkaSchatten.DiagonalCutoff4.collision_c327055_s2 (p : ℝ) (hpa : (89/16 : ℝ) ≤ p) (hpb : p ≤ (91/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (211611/100000 : ℝ) (32523/20000 : ℝ) (20519/25000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, true, true]])
    (hprev1 : (0 : ℝ) ≤ ((32951/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(32951/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(1681/5000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(1681/5000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(32733/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(32733/100000 : ℝ)*X 1 2)) : False := by sorry
