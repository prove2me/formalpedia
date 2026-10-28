-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_box_nonnegative_w1169
-- name    : HlawkaSchatten.DiagonalCutoff4.box_nonnegative_w1169
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-28T15:43:32.983154+00:00
-- url     : https://prove2.me/theorems/7e9ca2ab-5778-4caa-bca7-3b0dea36e55d
-- title:
--   Nonnegative Hlawka deficit in the certified coordinate box near exponent four
-- statement:
--   For the real exponent interval and the nine coordinate bounds stated formally, the sharp-constant Hlawka deficit is nonnegative. No normalization, sign-chart coverage, or universal localization is assumed beyond the displayed coordinate box. This is the local averaging step in the cutoff-four proof.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff4_Localization
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6 HlawkaSchatten.DiagonalCutoff4

theorem HlawkaSchatten.DiagonalCutoff4.box_nonnegative_w1169 (p : ℝ) (hpa : (8361/2048 : ℝ) ≤ p) (hpb : p ≤ (4181/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ)
    (hbox : ∀ j i, if j=i then -(12447/20000 : ℝ) ≤ X j i ∧ X j i ≤ -(59319/100000 : ℝ)
      else (7989/10000 : ℝ) ≤ X j i ∧ X j i ≤ (16637/20000 : ℝ)) :
    0 ≤ tripleDeficit p (cyclicConstant p) X := by sorry
