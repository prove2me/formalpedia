-- Prove2me | Theorems.Thm_O3_Stage8EuclideanMinimizer_lpNorm_two_sq_sub_decomposition
-- name    : O3.Stage8EuclideanMinimizer.lpNorm_two_sq_sub_decomposition
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T14:15:38.455384+00:00
-- url     : https://prove2.me/theorems/bf521a5e-4242-4d36-9576-9a21c8d34cb9
-- title:
--   Stage8 Euclidean Minimizer: lp Norm two sq sub decomposition
-- statement:
--   Polarization for the literal O3 `lpNorm 2`.
--
--   Source: https://github.com/yuningyang19/parameter_free_gradient_p/blob/f71215fa936fe01aff8a765c62b399e131df963b/O3/Stage8EuclideanMinimizer.lean#L30-L49
-- source:
--   https://github.com/yuningyang19/parameter_free_gradient_p/blob/f71215fa936fe01aff8a765c62b399e131df963b/O3/Stage8EuclideanMinimizer.lean#L30-L49

import Definitions.Def_O3_Foundation
import Definitions.Def_O3_Stage2RouteC
import Definitions.Def_O3_Stage2RouteD
import Definitions.Def_O3_Stage8EuclideanMinimizer
set_option autoImplicit true
open O3
open O3.Stage8EuclideanMinimizer

theorem O3.Stage8EuclideanMinimizer.lpNorm_two_sq_sub_decomposition {d : ℕ} (x z x₀ : Point d) :
    (lpNorm 2 (x - x₀)) ^ (2 : ℕ) =
      (lpNorm 2 (z - x₀)) ^ (2 : ℕ) +
        2 * pairing (z - x₀) (x - z) +
        (lpNorm 2 (x - z)) ^ (2 : ℕ) := by sorry
