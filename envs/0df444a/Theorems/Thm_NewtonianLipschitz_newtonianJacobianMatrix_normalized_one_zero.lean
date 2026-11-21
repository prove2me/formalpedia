-- Prove2me | Theorems.Thm_NewtonianLipschitz_newtonianJacobianMatrix_normalized_one_zero
-- name    : NewtonianLipschitz.newtonianJacobianMatrix_normalized_one_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T03:32:57.649496+00:00
-- url     : https://prove2.me/theorems/8ec89117-91e6-4eb1-92d4-54b5608b0e3b
-- title:
--   Newtonian Lipschitz: newtonian Jacobian Matrix normalized one zero
-- statement:
--   Exact entry in row one and column zero.
--
--   Source: https://github.com/alexodas/NewtonianLipschitzOptimality/blob/74f12a8510a4b0087b56f2b309e6ad99fbd26420/NewtonianLipschitz/NormalizedSharpBound.lean#L95-L101
-- source:
--   https://github.com/alexodas/NewtonianLipschitzOptimality/blob/74f12a8510a4b0087b56f2b309e6ad99fbd26420/NewtonianLipschitz/NormalizedSharpBound.lean#L95-L101

module
public import Definitions.Def_NewtonianLipschitz_JacobianMatrix
public import Definitions.Def_NewtonianLipschitz_ScalarMaximum
public import Definitions.Def_NewtonianLipschitz_NormalizedSharpBound
set_option autoImplicit true
@[expose] public section
public section
open NewtonianLipschitz

theorem NewtonianLipschitz.newtonianJacobianMatrix_normalized_one_zero
    (μ u v : ℝ) :
    newtonianJacobianMatrix μ (normalizedVector u v) 1 0 =
      (μ / euclideanRadius (normalizedVector u v) ^ 5) *
        (3 * u) := by sorry
