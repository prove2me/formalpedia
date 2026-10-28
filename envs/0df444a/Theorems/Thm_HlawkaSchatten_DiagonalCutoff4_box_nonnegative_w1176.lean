-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_box_nonnegative_w1176
-- name    : HlawkaSchatten.DiagonalCutoff4.box_nonnegative_w1176
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-28T15:46:24.183998+00:00
-- url     : https://prove2.me/theorems/dfd24085-7f9b-4865-a28b-1ba2ddbd890f
-- title:
--   Nonnegative Hlawka deficit in the certified coordinate box near exponent four
-- statement:
--   For the real exponent interval and the nine coordinate bounds stated formally, the sharp-constant Hlawka deficit is nonnegative. No normalization, sign-chart coverage, or universal localization is assumed beyond the displayed coordinate box. This is the local averaging step in the cutoff-four proof.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff4_Localization
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6 HlawkaSchatten.DiagonalCutoff4

theorem HlawkaSchatten.DiagonalCutoff4.box_nonnegative_w1176 (p : ℝ) (hpa : (523/128 : ℝ) ≤ p) (hpb : p ≤ (8369/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ)
    (hbox : ∀ j i, if j=i then -(12447/20000 : ℝ) ≤ X j i ∧ X j i ≤ -(2373/4000 : ℝ)
      else (9989/12500 : ℝ) ≤ X j i ∧ X j i ≤ (104/125 : ℝ)) :
    0 ≤ tripleDeficit p (cyclicConstant p) X := by sorry
