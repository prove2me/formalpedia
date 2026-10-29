-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c310061_s5
-- name    : HlawkaSchatten.DiagonalCutoff4.collision_c310061_s5
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-28T21:58:31.594708+00:00
-- url     : https://prove2.me/theorems/01d6d119-6f86-4caf-a6f8-d0d656462957
-- title:
--   Hlawka collision chart 310062, bounded proof step 6
-- statement:
--   For the normalized ordered chart on $[35/8,71/16]$ and the preceding tail-ratio bounds displayed formally, no such real triple exists.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff4_Localization
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6 HlawkaSchatten.DiagonalCutoff4

theorem HlawkaSchatten.DiagonalCutoff4.collision_c310061_s5 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (71/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (161793/100000 : ℝ) (18111/10000 : ℝ) (2431/3125 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, false, true]])
    (hprev4 : (0 : ℝ) ≤ ((5027/25000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(5027/25000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(493/2000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(493/2000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(22907/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(22907/100000 : ℝ)*X 1 2)) : False := by sorry
