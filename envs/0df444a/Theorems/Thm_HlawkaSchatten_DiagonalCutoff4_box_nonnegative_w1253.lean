-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_box_nonnegative_w1253
-- name    : HlawkaSchatten.DiagonalCutoff4.box_nonnegative_w1253
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-28T16:17:51.69362+00:00
-- url     : https://prove2.me/theorems/7c16096b-2166-4fd6-878b-fa25903be33f
-- title:
--   Nonnegative Hlawka deficit in the certified coordinate box near exponent four
-- statement:
--   For the real exponent interval and the nine coordinate bounds stated formally, the sharp-constant Hlawka deficit is nonnegative. No normalization, sign-chart coverage, or universal localization is assumed beyond the displayed coordinate box. This is the local averaging step in the cutoff-four proof.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff4_Localization
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6 HlawkaSchatten.DiagonalCutoff4

theorem HlawkaSchatten.DiagonalCutoff4.box_nonnegative_w1253 (p : ℝ) (hpa : (8445/2048 : ℝ) ≤ p) (hpb : p ≤ (4223/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ)
    (hbox : ∀ j i, if j=i then -(62249/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(29693/50000 : ℝ)
      else (80141/100000 : ℝ) ≤ X j i ∧ X j i ≤ (8337/10000 : ℝ)) :
    0 ≤ tripleDeficit p (cyclicConstant p) X := by sorry
