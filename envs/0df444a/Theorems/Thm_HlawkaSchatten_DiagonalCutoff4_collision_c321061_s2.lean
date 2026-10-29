-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c321061_s2
-- name    : HlawkaSchatten.DiagonalCutoff4.collision_c321061_s2
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-29T00:40:23.656557+00:00
-- url     : https://prove2.me/theorems/32f516c4-ef43-4ef0-9cfc-fae1ee91288f
-- title:
--   Hlawka collision chart 321062, bounded proof step 3
-- statement:
--   For the normalized ordered chart on $[81/16,41/8]$ and the preceding tail-ratio bounds displayed formally, no such real triple exists.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff4_Localization
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6 HlawkaSchatten.DiagonalCutoff4

theorem HlawkaSchatten.DiagonalCutoff4.collision_c321061_s2 (p : ℝ) (hpa : (81/16 : ℝ) ≤ p) (hpb : p ≤ (41/8 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (11897/6250 : ℝ) (168549/100000 : ℝ) (80491/100000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, false, true]])
    (hprev1 : (0 : ℝ) ≤ ((7683/20000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(7683/20000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(45359/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(45359/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(20193/50000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(20193/50000 : ℝ)*X 1 2)) : False := by sorry
