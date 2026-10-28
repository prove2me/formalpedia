-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_box_nonnegative_w1256
-- name    : HlawkaSchatten.DiagonalCutoff4.box_nonnegative_w1256
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-28T13:29:12.001376+00:00
-- url     : https://prove2.me/theorems/a5d2c8c9-05ed-4c25-890c-06a119ccf25f
-- title:
--   Nonnegative Hlawka deficit in the certified coordinate box near exponent four
-- statement:
--   For the real exponent interval and the nine coordinate bounds stated formally, the sharp-constant Hlawka deficit is nonnegative. No normalization, sign-chart coverage, or universal localization is assumed beyond the displayed coordinate box. This is the local averaging step in the cutoff-four proof.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff4_Localization
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6 HlawkaSchatten.DiagonalCutoff4

theorem HlawkaSchatten.DiagonalCutoff4.box_nonnegative_w1256 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (8449/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ)
    (hbox : ∀ j i, if j=i then -(62249/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(59389/100000 : ℝ)
      else (1603/2000 : ℝ) ≤ X j i ∧ X j i ≤ (5211/6250 : ℝ)) :
    0 ≤ tripleDeficit p (cyclicConstant p) X := by sorry
