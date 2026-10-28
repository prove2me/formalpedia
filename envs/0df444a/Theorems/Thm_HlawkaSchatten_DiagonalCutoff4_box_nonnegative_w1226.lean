-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_box_nonnegative_w1226
-- name    : HlawkaSchatten.DiagonalCutoff4.box_nonnegative_w1226
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-28T16:07:12.724238+00:00
-- url     : https://prove2.me/theorems/474e44e6-c434-4e6c-afe1-b5a1b5459cda
-- title:
--   Nonnegative Hlawka deficit in the certified coordinate box near exponent four
-- statement:
--   For the real exponent interval and the nine coordinate bounds stated formally, the sharp-constant Hlawka deficit is nonnegative. No normalization, sign-chart coverage, or universal localization is assumed beyond the displayed coordinate box. This is the local averaging step in the cutoff-four proof.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff4_Localization
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6 HlawkaSchatten.DiagonalCutoff4

theorem HlawkaSchatten.DiagonalCutoff4.box_nonnegative_w1226 (p : ℝ) (hpa : (4209/1024 : ℝ) ≤ p) (hpb : p ≤ (8419/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ)
    (hbox : ∀ j i, if j=i then -(15561/25000 : ℝ) ≤ X j i ∧ X j i ≤ -(11873/20000 : ℝ)
      else (40031/50000 : ℝ) ≤ X j i ∧ X j i ≤ (83311/100000 : ℝ)) :
    0 ≤ tripleDeficit p (cyclicConstant p) X := by sorry
