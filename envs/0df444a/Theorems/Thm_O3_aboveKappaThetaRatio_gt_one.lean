-- Prove2me | Theorems.Thm_O3_aboveKappaThetaRatio_gt_one
-- name    : O3.aboveKappaThetaRatio_gt_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T14:05:32.852807+00:00
-- url     : https://prove2.me/theorems/cb33166e-e0a3-548b-9450-caae249a34a5
-- title:
--   O3: above Kappa Theta Ratio gt one
-- statement:
--   The O3 construction uses the above Kappa Theta Ratio gt one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/yuningyang19/parameter_free_gradient_p/blob/f71215fa936fe01aff8a765c62b399e131df963b/O3/AboveTwo.lean#L294-L302
-- source:
--   https://github.com/yuningyang19/parameter_free_gradient_p/blob/f71215fa936fe01aff8a765c62b399e131df963b/O3/AboveTwo.lean#L294-L302

import Definitions.Def_O3_Foundation
import Definitions.Def_O3_AboveTwo
set_option autoImplicit true
open scoped BigOperators
open O3

theorem O3.aboveKappaThetaRatio_gt_one {p kappa : ℝ}
    (hp : AboveTwoRegime p) (hkappa : 1 < kappa) :
    1 < 8 * kappa ^ 2 / (aboveTheta p) ^ 2 := by sorry
