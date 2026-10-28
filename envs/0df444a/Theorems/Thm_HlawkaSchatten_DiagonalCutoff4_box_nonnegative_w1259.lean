-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_box_nonnegative_w1259
-- name    : HlawkaSchatten.DiagonalCutoff4.box_nonnegative_w1259
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-28T16:40:11.097191+00:00
-- url     : https://prove2.me/theorems/76b28096-cd3f-47af-a745-477454e74013
-- title:
--   Nonnegative Hlawka deficit in the certified coordinate box near exponent four
-- statement:
--   For the real exponent interval and the nine coordinate bounds stated formally, the sharp-constant Hlawka deficit is nonnegative. No normalization, sign-chart coverage, or universal localization is assumed beyond the displayed coordinate box. This is the local averaging step in the cutoff-four proof.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff4_Localization
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6 HlawkaSchatten.DiagonalCutoff4

theorem HlawkaSchatten.DiagonalCutoff4.box_nonnegative_w1259 (p : ℝ) (hpa : (8451/2048 : ℝ) ≤ p) (hpb : p ≤ (2113/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ)
    (hbox : ∀ j i, if j=i then -(249/400 : ℝ) ≤ X j i ∧ X j i ≤ -(59391/100000 : ℝ)
      else (80159/100000 : ℝ) ≤ X j i ∧ X j i ≤ (83383/100000 : ℝ)) :
    0 ≤ tripleDeficit p (cyclicConstant p) X := by sorry
