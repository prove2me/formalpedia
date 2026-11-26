-- Prove2me | Theorems.Thm_O3_Stage8EuclideanMinimizer_euclideanPsi_eq_min_add_sq
-- name    : O3.Stage8EuclideanMinimizer.euclideanPsi_eq_min_add_sq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T14:15:33.38143+00:00
-- url     : https://prove2.me/theorems/09deccbc-d21a-54b5-87cd-f3863d3390b7
-- title:
--   Stage8 Euclidean Minimizer: euclidean Psi eq min add sq
-- statement:
--   Exact completion-of-the-square identity.  This is stronger than the
--   needed lower bound and exposes the precise `M / 2` coefficient.
--
--   Source: https://github.com/yuningyang19/parameter_free_gradient_p/blob/f71215fa936fe01aff8a765c62b399e131df963b/O3/Stage8EuclideanMinimizer.lean#L83-L100
-- source:
--   https://github.com/yuningyang19/parameter_free_gradient_p/blob/f71215fa936fe01aff8a765c62b399e131df963b/O3/Stage8EuclideanMinimizer.lean#L83-L100

import Definitions.Def_O3_Foundation
import Definitions.Def_O3_Stage2RouteC
import Definitions.Def_O3_Stage2RouteD
import Definitions.Def_O3_Stage8EuclideanMinimizer
set_option autoImplicit true
open O3
open O3.Stage8EuclideanMinimizer

theorem O3.Stage8EuclideanMinimizer.euclideanPsi_eq_min_add_sq {M : ℝ} (hM : M ≠ 0) {d : ℕ}
    (x₀ s : Point d) (c : ℝ) (x : Point d) :
    euclideanPsi M x₀ s c x =
      euclideanPsi M x₀ s c (euclideanPsiMinimizer M x₀ s) +
        M / 2 *
          (lpNorm 2 (x - euclideanPsiMinimizer M x₀ s)) ^ (2 : ℕ) := by sorry
