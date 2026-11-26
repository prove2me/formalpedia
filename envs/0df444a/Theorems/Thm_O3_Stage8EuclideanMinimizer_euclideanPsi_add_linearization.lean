-- Prove2me | Theorems.Thm_O3_Stage8EuclideanMinimizer_euclideanPsi_add_linearization
-- name    : O3.Stage8EuclideanMinimizer.euclideanPsi_add_linearization
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T14:16:03.37224+00:00
-- url     : https://prove2.me/theorems/3d33154f-ec31-5bd7-b377-6b3524a65962
-- title:
--   Stage8 Euclidean Minimizer: euclidean Psi add linearization
-- statement:
--   Adding one weighted oracle linearization preserves the canonical form,
--   with the accumulated gradient and affine constant updated exactly.
--
--   Source: https://github.com/yuningyang19/parameter_free_gradient_p/blob/f71215fa936fe01aff8a765c62b399e131df963b/O3/Stage8EuclideanMinimizer.lean#L130-L141
-- source:
--   https://github.com/yuningyang19/parameter_free_gradient_p/blob/f71215fa936fe01aff8a765c62b399e131df963b/O3/Stage8EuclideanMinimizer.lean#L130-L141

import Definitions.Def_O3_Foundation
import Definitions.Def_O3_Stage2RouteC
import Definitions.Def_O3_Stage2RouteD
import Definitions.Def_O3_Stage8EuclideanMinimizer
set_option autoImplicit true
open O3
open O3.Stage8EuclideanMinimizer

theorem O3.Stage8EuclideanMinimizer.euclideanPsi_add_linearization {M a fy : ℝ} {d : ℕ}
    (x₀ s g y : Point d) (c : ℝ) (x : Point d) :
    euclideanPsi M x₀ s c x + a * (fy + pairing g (x - y)) =
      euclideanPsi M x₀ (s + a • g)
        (c + a * (fy + pairing g (x₀ - y))) x := by sorry
