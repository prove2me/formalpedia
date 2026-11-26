-- Prove2me | Theorems.Thm_O3_abovePhaseCoefficient_eq
-- name    : O3.abovePhaseCoefficient_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T14:03:45.732806+00:00
-- url     : https://prove2.me/theorems/a82641ea-c1ea-5974-8b9f-a11ec5860453
-- title:
--   O3: above Phase Coefficient eq
-- statement:
--   The source coefficient `c_t=t/(t+1)` and its bound by one.
--
--   Source: https://github.com/yuningyang19/parameter_free_gradient_p/blob/f71215fa936fe01aff8a765c62b399e131df963b/O3/AboveTwo.lean#L114-L122
-- source:
--   https://github.com/yuningyang19/parameter_free_gradient_p/blob/f71215fa936fe01aff8a765c62b399e131df963b/O3/AboveTwo.lean#L114-L122

import Definitions.Def_O3_Foundation
import Definitions.Def_O3_AboveTwo
set_option autoImplicit true
open scoped BigOperators
open O3

theorem O3.abovePhaseCoefficient_eq {M : ℝ} (hM : M ≠ 0) {t : ℕ} (ht : 1 ≤ t) :
    M * (aboveStepWeight M t) ^ 2 /
        (2 * aboveAccumulatedWeight M t) =
      (t : ℝ) / (t + 1 : ℕ) := by sorry
