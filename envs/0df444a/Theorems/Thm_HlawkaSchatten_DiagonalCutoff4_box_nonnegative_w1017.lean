-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_box_nonnegative_w1017
-- name    : HlawkaSchatten.DiagonalCutoff4.box_nonnegative_w1017
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-28T13:06:26.149085+00:00
-- url     : https://prove2.me/theorems/f84aedca-ffd7-4021-a80a-9835813f0718
-- title:
--   Nonnegative Hlawka deficit in the certified coordinate box near exponent four
-- statement:
--   For the real exponent interval and the nine coordinate bounds stated formally, the sharp-constant Hlawka deficit is nonnegative. No normalization, sign-chart coverage, or universal localization is assumed beyond the displayed coordinate box. This is the local averaging step in the cutoff-four proof.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff4_Localization
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6 HlawkaSchatten.DiagonalCutoff4

theorem HlawkaSchatten.DiagonalCutoff4.box_nonnegative_w1017 (p : ℝ) (hpa : (8209/2048 : ℝ) ≤ p) (hpb : p ≤ (4105/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ)
    (hbox : ∀ j i, if j=i then -(62223/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(11841/20000 : ℝ)
      else (79417/100000 : ℝ) ≤ X j i ∧ X j i ≤ (2071/2500 : ℝ)) :
    0 ≤ tripleDeficit p (cyclicConstant p) X := by sorry
