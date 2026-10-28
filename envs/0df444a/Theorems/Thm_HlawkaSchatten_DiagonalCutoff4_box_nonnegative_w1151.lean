-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_box_nonnegative_w1151
-- name    : HlawkaSchatten.DiagonalCutoff4.box_nonnegative_w1151
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-28T15:34:38.466202+00:00
-- url     : https://prove2.me/theorems/bc4156ab-45f3-472b-94e6-ff1b558a2116
-- title:
--   Nonnegative Hlawka deficit in the certified coordinate box near exponent four
-- statement:
--   For the real exponent interval and the nine coordinate bounds stated formally, the sharp-constant Hlawka deficit is nonnegative. No normalization, sign-chart coverage, or universal localization is assumed beyond the displayed coordinate box. This is the local averaging step in the cutoff-four proof.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff4_Localization
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6 HlawkaSchatten.DiagonalCutoff4

theorem HlawkaSchatten.DiagonalCutoff4.box_nonnegative_w1151 (p : ℝ) (hpa : (8343/2048 : ℝ) ≤ p) (hpb : p ≤ (1043/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ)
    (hbox : ∀ j i, if j=i then -(7779/12500 : ℝ) ≤ X j i ∧ X j i ≤ -(29653/50000 : ℝ)
      else (19959/25000 : ℝ) ≤ X j i ∧ X j i ≤ (10393/12500 : ℝ)) :
    0 ≤ tripleDeficit p (cyclicConstant p) X := by sorry
