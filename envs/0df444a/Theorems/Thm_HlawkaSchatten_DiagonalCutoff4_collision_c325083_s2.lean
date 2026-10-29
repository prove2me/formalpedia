-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c325083_s2
-- name    : HlawkaSchatten.DiagonalCutoff4.collision_c325083_s2
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-29T00:52:30.23869+00:00
-- url     : https://prove2.me/theorems/2d8d66d3-acfe-4f42-8be7-e48bcb516f2b
-- title:
--   Hlawka collision chart 325084, bounded proof step 3
-- statement:
--   For the normalized ordered chart on $[85/16,87/16]$ and the preceding tail-ratio bounds displayed formally, no such real triple exists.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff4_Localization
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6 HlawkaSchatten.DiagonalCutoff4

theorem HlawkaSchatten.DiagonalCutoff4.collision_c325083_s2 (p : ℝ) (hpa : (85/16 : ℝ) ≤ p) (hpb : p ≤ (87/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (200939/100000 : ℝ) (33069/20000 : ℝ) (81317/100000 : ℝ) X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, true, true], ![true, true, true]])
    (hprev1 : (0 : ℝ) ≤ ((1107/6250 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(1107/6250 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((2309/12500 : ℝ)*X 0 1+(-1 : ℝ)*X 0 2+(2309/12500 : ℝ)*X 2 1+(-1 : ℝ)*X 2 2) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(3741/20000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(3741/20000 : ℝ)*X 1 2)) : False := by sorry
