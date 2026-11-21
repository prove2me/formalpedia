-- Prove2me | Theorems.Thm_NewtonianLipschitz_newtonianJacobianMatrix_normalized_one_two
-- name    : NewtonianLipschitz.newtonianJacobianMatrix_normalized_one_two
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T03:29:48.288835+00:00
-- url     : https://prove2.me/theorems/2c30b513-2aab-4d01-8cca-370dcc5d998a
-- title:
--   Newtonian Lipschitz: newtonian Jacobian Matrix normalized one two
-- statement:
--   Exact entry in row one and column two.
--
--   Source: https://github.com/alexodas/NewtonianLipschitzOptimality/blob/74f12a8510a4b0087b56f2b309e6ad99fbd26420/NewtonianLipschitz/NormalizedSharpBound.lean#L114-L120
-- source:
--   https://github.com/alexodas/NewtonianLipschitzOptimality/blob/74f12a8510a4b0087b56f2b309e6ad99fbd26420/NewtonianLipschitz/NormalizedSharpBound.lean#L114-L120

module
public import Definitions.Def_NewtonianLipschitz_JacobianMatrix
public import Definitions.Def_NewtonianLipschitz_ScalarMaximum
public import Definitions.Def_NewtonianLipschitz_NormalizedSharpBound
set_option autoImplicit true
@[expose] public section
public section
open NewtonianLipschitz

theorem NewtonianLipschitz.newtonianJacobianMatrix_normalized_one_two
    (μ u v : ℝ) :
    newtonianJacobianMatrix μ (normalizedVector u v) 1 2 =
      (μ / euclideanRadius (normalizedVector u v) ^ 5) *
        (3 * u * v) := by sorry
