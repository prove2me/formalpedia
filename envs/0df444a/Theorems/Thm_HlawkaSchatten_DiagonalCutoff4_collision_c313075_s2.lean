-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c313075_s2
-- name    : HlawkaSchatten.DiagonalCutoff4.collision_c313075_s2
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-28T23:53:31.418699+00:00
-- url     : https://prove2.me/theorems/33d988ac-a2b9-4e72-baf0-b3d0bec0967a
-- title:
--   Hlawka collision chart 313076, bounded proof step 3
-- statement:
--   For the normalized ordered chart on $[73/16,37/8]$ and the preceding tail-ratio bounds displayed formally, no such real triple exists.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff4_Localization
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6 HlawkaSchatten.DiagonalCutoff4

theorem HlawkaSchatten.DiagonalCutoff4.collision_c313075_s2 (p : ℝ) (hpa : (73/16 : ℝ) ≤ p) (hpb : p ≤ (37/8 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (169487/100000 : ℝ) (176973/100000 : ℝ) (78599/100000 : ℝ) X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, false, true], ![true, false, true]])
    (hprev1 : (0 : ℝ) ≤ ((26191/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(26191/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-45261/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 0 2+(-45261/100000 : ℝ)*X 2 1+(-1 : ℝ)*X 2 2) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(16183/50000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(16183/50000 : ℝ)*X 1 2)) : False := by sorry
