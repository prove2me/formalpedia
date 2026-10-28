-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_box_nonnegative_w1149
-- name    : HlawkaSchatten.DiagonalCutoff4.box_nonnegative_w1149
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-28T15:34:15.89249+00:00
-- url     : https://prove2.me/theorems/5054a1b2-5743-4487-8611-1aedf588d607
-- title:
--   Nonnegative Hlawka deficit in the certified coordinate box near exponent four
-- statement:
--   For the real exponent interval and the nine coordinate bounds stated formally, the sharp-constant Hlawka deficit is nonnegative. No normalization, sign-chart coverage, or universal localization is assumed beyond the displayed coordinate box. This is the local averaging step in the cutoff-four proof.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff4_Localization
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6 HlawkaSchatten.DiagonalCutoff4

theorem HlawkaSchatten.DiagonalCutoff4.box_nonnegative_w1149 (p : ℝ) (hpa : (8341/2048 : ℝ) ≤ p) (hpb : p ≤ (4171/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ)
    (hbox : ∀ j i, if j=i then -(7779/12500 : ℝ) ≤ X j i ∧ X j i ≤ -(7413/12500 : ℝ)
      else (7983/10000 : ℝ) ≤ X j i ∧ X j i ≤ (4157/5000 : ℝ)) :
    0 ≤ tripleDeficit p (cyclicConstant p) X := by sorry
