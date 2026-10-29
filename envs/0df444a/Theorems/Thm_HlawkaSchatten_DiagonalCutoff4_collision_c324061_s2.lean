-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c324061_s2
-- name    : HlawkaSchatten.DiagonalCutoff4.collision_c324061_s2
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-29T00:49:12.52597+00:00
-- url     : https://prove2.me/theorems/b64698b1-bd09-4641-8170-de99100c2ca3
-- title:
--   Hlawka collision chart 324062, bounded proof step 3
-- statement:
--   For the normalized ordered chart on $[21/4,85/16]$ and the preceding tail-ratio bounds displayed formally, no such real triple exists.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff4_Localization
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6 HlawkaSchatten.DiagonalCutoff4

theorem HlawkaSchatten.DiagonalCutoff4.collision_c324061_s2 (p : ℝ) (hpa : (21/4 : ℝ) ≤ p) (hpb : p ≤ (85/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (49571/25000 : ℝ) (83049/50000 : ℝ) (81117/100000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, false, true]])
    (hprev1 : (0 : ℝ) ≤ ((31147/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(31147/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(9471/25000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(9471/25000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(8527/25000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(8527/25000 : ℝ)*X 1 2)) : False := by sorry
