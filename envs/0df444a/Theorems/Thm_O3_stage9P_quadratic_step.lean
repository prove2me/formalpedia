-- Prove2me | Theorems.Thm_O3_stage9P_quadratic_step
-- name    : O3.stage9P_quadratic_step
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T14:27:00.657935+00:00
-- url     : https://prove2.me/theorems/1d7f2353-63c1-4ca0-b95c-18494d247981
-- title:
--   O3: stage9 P quadratic step
-- statement:
--   The auxiliary recurrence converts the mixed product to a difference of
--   squares with the exact `theta_k^2` coefficient.
--
--   Source: https://github.com/yuningyang19/parameter_free_gradient_p/blob/f71215fa936fe01aff8a765c62b399e131df963b/O3/Stage9Telescoping.lean#L161-L177
-- source:
--   https://github.com/yuningyang19/parameter_free_gradient_p/blob/f71215fa936fe01aff8a765c62b399e131df963b/O3/Stage9Telescoping.lean#L161-L177

import Definitions.Def_O3_Foundation
import Definitions.Def_O3_Stage2RouteC
import Definitions.Def_O3_Stage2RouteD
import Definitions.Def_O3_Stage9Telescoping
set_option autoImplicit true
open scoped BigOperators
open O3

theorem O3.stage9P_quadratic_step {d : ℕ} {theta : ℕ → ℝ}
    {g : ℕ → Vec d} {k : ℕ} (hθ : theta k ≠ 0) :
    theta k * pairing (stage9P theta g k - g k)
        (stage9P theta g k + stage9P theta g (k + 1)) =
      (theta k) ^ 2 *
        ((lpNorm 2 (stage9P theta g k)) ^ (2 : ℕ) -
          (lpNorm 2 (stage9P theta g (k + 1))) ^ (2 : ℕ)) := by sorry
