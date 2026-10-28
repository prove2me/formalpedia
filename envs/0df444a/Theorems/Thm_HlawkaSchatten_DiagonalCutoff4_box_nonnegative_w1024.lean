-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_box_nonnegative_w1024
-- name    : HlawkaSchatten.DiagonalCutoff4.box_nonnegative_w1024
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-28T13:14:30.428356+00:00
-- url     : https://prove2.me/theorems/6099a571-e149-4d89-a4c8-f56839959800
-- title:
--   Nonnegative Hlawka deficit in the certified coordinate box near exponent four
-- statement:
--   For the real exponent interval and the nine coordinate bounds stated formally, the sharp-constant Hlawka deficit is nonnegative. No normalization, sign-chart coverage, or universal localization is assumed beyond the displayed coordinate box. This is the local averaging step in the cutoff-four proof.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff4_Localization
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6 HlawkaSchatten.DiagonalCutoff4

theorem HlawkaSchatten.DiagonalCutoff4.box_nonnegative_w1024 (p : ℝ) (hpa : (1027/256 : ℝ) ≤ p) (hpb : p ≤ (8217/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ)
    (hbox : ∀ j i, if j=i then -(62223/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(5921/10000 : ℝ)
      else (79439/100000 : ℝ) ≤ X j i ∧ X j i ≤ (10357/12500 : ℝ)) :
    0 ≤ tripleDeficit p (cyclicConstant p) X := by sorry
