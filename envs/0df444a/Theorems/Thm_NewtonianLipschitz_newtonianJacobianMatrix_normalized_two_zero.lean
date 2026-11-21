-- Prove2me | Theorems.Thm_NewtonianLipschitz_newtonianJacobianMatrix_normalized_two_zero
-- name    : NewtonianLipschitz.newtonianJacobianMatrix_normalized_two_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T03:33:26.436429+00:00
-- url     : https://prove2.me/theorems/9fd437b1-d854-44af-8693-9077497ed108
-- title:
--   Newtonian Lipschitz: newtonian Jacobian Matrix normalized two zero
-- statement:
--   Entry (2,0) in nonnegative normalized coordinates.
--
--   Source: https://github.com/alexodas/NewtonianLipschitzOptimality/blob/74f12a8510a4b0087b56f2b309e6ad99fbd26420/NewtonianLipschitz/NormalizedSharpBound.lean#L188-L194
-- source:
--   https://github.com/alexodas/NewtonianLipschitzOptimality/blob/74f12a8510a4b0087b56f2b309e6ad99fbd26420/NewtonianLipschitz/NormalizedSharpBound.lean#L188-L194

module
public import Definitions.Def_NewtonianLipschitz_JacobianMatrix
public import Definitions.Def_NewtonianLipschitz_ScalarMaximum
public import Definitions.Def_NewtonianLipschitz_NormalizedSharpBound
set_option autoImplicit true
@[expose] public section
public section
open NewtonianLipschitz

theorem NewtonianLipschitz.newtonianJacobianMatrix_normalized_two_zero
    (μ u v : ℝ) :
    newtonianJacobianMatrix μ (normalizedVector u v) 2 0 =
      (μ / euclideanRadius (normalizedVector u v) ^ 5) *
        (3 * v) := by sorry
