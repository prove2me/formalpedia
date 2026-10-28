-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_box_nonnegative_w1078
-- name    : HlawkaSchatten.DiagonalCutoff4.box_nonnegative_w1078
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-28T14:47:40.624167+00:00
-- url     : https://prove2.me/theorems/9d5a5036-7f29-4933-9199-d5639b2c728d
-- title:
--   Nonnegative Hlawka deficit in the certified coordinate box near exponent four
-- statement:
--   For the real exponent interval and the nine coordinate bounds stated formally, the sharp-constant Hlawka deficit is nonnegative. No normalization, sign-chart coverage, or universal localization is assumed beyond the displayed coordinate box. This is the local averaging step in the cutoff-four proof.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff4_Localization
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6 HlawkaSchatten.DiagonalCutoff4

theorem HlawkaSchatten.DiagonalCutoff4.box_nonnegative_w1078 (p : ℝ) (hpa : (4135/1024 : ℝ) ≤ p) (hpb : p ≤ (8271/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ)
    (hbox : ∀ j i, if j=i then -(2489/4000 : ℝ) ≤ X j i ∧ X j i ≤ -(237/400 : ℝ)
      else (7961/10000 : ℝ) ≤ X j i ∧ X j i ≤ (4149/5000 : ℝ)) :
    0 ≤ tripleDeficit p (cyclicConstant p) X := by sorry
