-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_box_nonnegative_w1152
-- name    : HlawkaSchatten.DiagonalCutoff4.box_nonnegative_w1152
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-28T15:35:18.087879+00:00
-- url     : https://prove2.me/theorems/ee8fdf57-bb9a-4db5-b402-0b8504a0b1a9
-- title:
--   Nonnegative Hlawka deficit in the certified coordinate box near exponent four
-- statement:
--   For the real exponent interval and the nine coordinate bounds stated formally, the sharp-constant Hlawka deficit is nonnegative. No normalization, sign-chart coverage, or universal localization is assumed beyond the displayed coordinate box. This is the local averaging step in the cutoff-four proof.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff4_Localization
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6 HlawkaSchatten.DiagonalCutoff4

theorem HlawkaSchatten.DiagonalCutoff4.box_nonnegative_w1152 (p : ℝ) (hpa : (1043/256 : ℝ) ≤ p) (hpb : p ≤ (8345/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ)
    (hbox : ∀ j i, if j=i then -(7779/12500 : ℝ) ≤ X j i ∧ X j i ≤ -(29653/50000 : ℝ)
      else (79839/100000 : ℝ) ≤ X j i ∧ X j i ≤ (83147/100000 : ℝ)) :
    0 ≤ tripleDeficit p (cyclicConstant p) X := by sorry
