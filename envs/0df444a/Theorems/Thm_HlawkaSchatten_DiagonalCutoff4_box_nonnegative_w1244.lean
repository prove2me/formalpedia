-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_box_nonnegative_w1244
-- name    : HlawkaSchatten.DiagonalCutoff4.box_nonnegative_w1244
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-28T16:14:05.994981+00:00
-- url     : https://prove2.me/theorems/6d2503a6-dd27-4882-8fb9-ab4ff27d9e0d
-- title:
--   Nonnegative Hlawka deficit in the certified coordinate box near exponent four
-- statement:
--   For the real exponent interval and the nine coordinate bounds stated formally, the sharp-constant Hlawka deficit is nonnegative. No normalization, sign-chart coverage, or universal localization is assumed beyond the displayed coordinate box. This is the local averaging step in the cutoff-four proof.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff4_Localization
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6 HlawkaSchatten.DiagonalCutoff4

theorem HlawkaSchatten.DiagonalCutoff4.box_nonnegative_w1244 (p : ℝ) (hpa : (2109/512 : ℝ) ≤ p) (hpb : p ≤ (8437/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ)
    (hbox : ∀ j i, if j=i then -(62247/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(59379/100000 : ℝ)
      else (16023/20000 : ℝ) ≤ X j i ∧ X j i ≤ (1667/2000 : ℝ)) :
    0 ≤ tripleDeficit p (cyclicConstant p) X := by sorry
