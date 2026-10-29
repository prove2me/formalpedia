-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c313060_s2
-- name    : HlawkaSchatten.DiagonalCutoff4.collision_c313060_s2
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-28T23:52:59.275164+00:00
-- url     : https://prove2.me/theorems/6b26cef1-4063-473f-8ed3-bb041f670fa7
-- title:
--   Hlawka collision chart 313061, bounded proof step 3
-- statement:
--   For the normalized ordered chart on $[73/16,37/8]$ and the preceding tail-ratio bounds displayed formally, no such real triple exists.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff4_Localization
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6 HlawkaSchatten.DiagonalCutoff4

theorem HlawkaSchatten.DiagonalCutoff4.collision_c313060_s2 (p : ℝ) (hpa : (73/16 : ℝ) ≤ p) (hpb : p ≤ (37/8 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (169487/100000 : ℝ) (176973/100000 : ℝ) (78599/100000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, false, false]])
    (hprev1 : (0 : ℝ) ≤ ((31029/50000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(31029/50000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(31911/50000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(31911/50000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-24613/50000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-24613/50000 : ℝ)*X 1 2)) : False := by sorry
