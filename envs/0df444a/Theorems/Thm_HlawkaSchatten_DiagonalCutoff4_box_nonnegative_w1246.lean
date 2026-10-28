-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_box_nonnegative_w1246
-- name    : HlawkaSchatten.DiagonalCutoff4.box_nonnegative_w1246
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-28T16:14:50.01787+00:00
-- url     : https://prove2.me/theorems/a4e3483f-0ae4-4c3e-a693-1f983df34a6d
-- title:
--   Nonnegative Hlawka deficit in the certified coordinate box near exponent four
-- statement:
--   For the real exponent interval and the nine coordinate bounds stated formally, the sharp-constant Hlawka deficit is nonnegative. No normalization, sign-chart coverage, or universal localization is assumed beyond the displayed coordinate box. This is the local averaging step in the cutoff-four proof.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff4_Localization
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6 HlawkaSchatten.DiagonalCutoff4

theorem HlawkaSchatten.DiagonalCutoff4.box_nonnegative_w1246 (p : ℝ) (hpa : (4219/1024 : ℝ) ≤ p) (hpb : p ≤ (8439/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ)
    (hbox : ∀ j i, if j=i then -(62247/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(59381/100000 : ℝ)
      else (80121/100000 : ℝ) ≤ X j i ∧ X j i ≤ (41677/50000 : ℝ)) :
    0 ≤ tripleDeficit p (cyclicConstant p) X := by sorry
