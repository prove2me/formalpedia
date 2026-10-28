-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_box_nonnegative_w1028
-- name    : HlawkaSchatten.DiagonalCutoff4.box_nonnegative_w1028
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-28T13:21:11.415886+00:00
-- url     : https://prove2.me/theorems/0b90e29f-7958-4b4b-9fc2-56aedaf79d7b
-- title:
--   Nonnegative Hlawka deficit in the certified coordinate box near exponent four
-- statement:
--   For the real exponent interval and the nine coordinate bounds stated formally, the sharp-constant Hlawka deficit is nonnegative. No normalization, sign-chart coverage, or universal localization is assumed beyond the displayed coordinate box. This is the local averaging step in the cutoff-four proof.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff4_Localization
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6 HlawkaSchatten.DiagonalCutoff4

theorem HlawkaSchatten.DiagonalCutoff4.box_nonnegative_w1028 (p : ℝ) (hpa : (2055/512 : ℝ) ≤ p) (hpb : p ≤ (8221/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ)
    (hbox : ∀ j i, if j=i then -(62223/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(59213/100000 : ℝ)
      else (19863/25000 : ℝ) ≤ X j i ∧ X j i ≤ (16573/20000 : ℝ)) :
    0 ≤ tripleDeficit p (cyclicConstant p) X := by sorry
