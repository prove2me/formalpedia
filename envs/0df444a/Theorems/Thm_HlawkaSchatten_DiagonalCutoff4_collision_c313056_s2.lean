-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c313056_s2
-- name    : HlawkaSchatten.DiagonalCutoff4.collision_c313056_s2
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-28T23:52:15.987987+00:00
-- url     : https://prove2.me/theorems/f3300649-d0e5-43f9-bc39-edd4906e08c8
-- title:
--   Hlawka collision chart 313057, bounded proof step 3
-- statement:
--   For the normalized ordered chart on $[73/16,37/8]$ and the preceding tail-ratio bounds displayed formally, no such real triple exists.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff4_Localization
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6 HlawkaSchatten.DiagonalCutoff4

theorem HlawkaSchatten.DiagonalCutoff4.collision_c313056_s2 (p : ℝ) (hpa : (73/16 : ℝ) ≤ p) (hpb : p ≤ (37/8 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (169487/100000 : ℝ) (176973/100000 : ℝ) (78599/100000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![false, false, false]])
    (hprev1 : (0 : ℝ) ≤ ((1093/3125 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(1093/3125 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(1093/3125 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(1093/3125 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(-1017/100000 : ℝ)*X 0 2+(1 : ℝ)*X 1 0+(-1017/100000 : ℝ)*X 1 2)) : False := by sorry
