-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_box_nonnegative_w1093
-- name    : HlawkaSchatten.DiagonalCutoff4.box_nonnegative_w1093
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-28T14:56:38.109994+00:00
-- url     : https://prove2.me/theorems/2330c2a4-7a7a-42c3-b2f5-0e00451a8f48
-- title:
--   Nonnegative Hlawka deficit in the certified coordinate box near exponent four
-- statement:
--   For the real exponent interval and the nine coordinate bounds stated formally, the sharp-constant Hlawka deficit is nonnegative. No normalization, sign-chart coverage, or universal localization is assumed beyond the displayed coordinate box. This is the local averaging step in the cutoff-four proof.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff4_Localization
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6 HlawkaSchatten.DiagonalCutoff4

theorem HlawkaSchatten.DiagonalCutoff4.box_nonnegative_w1093 (p : ℝ) (hpa : (8285/2048 : ℝ) ≤ p) (hpb : p ≤ (4143/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ)
    (hbox : ∀ j i, if j=i then -(31113/50000 : ℝ) ≤ X j i ∧ X j i ≤ -(59261/100000 : ℝ)
      else (79657/100000 : ℝ) ≤ X j i ∧ X j i ≤ (41507/50000 : ℝ)) :
    0 ≤ tripleDeficit p (cyclicConstant p) X := by sorry
