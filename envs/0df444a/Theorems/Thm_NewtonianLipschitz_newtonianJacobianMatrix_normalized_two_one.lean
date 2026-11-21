-- Prove2me | Theorems.Thm_NewtonianLipschitz_newtonianJacobianMatrix_normalized_two_one
-- name    : NewtonianLipschitz.newtonianJacobianMatrix_normalized_two_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T03:29:49.26977+00:00
-- url     : https://prove2.me/theorems/649bd2de-1ed5-4106-a4ad-6708cc9212ac
-- title:
--   Newtonian Lipschitz: newtonian Jacobian Matrix normalized two one
-- statement:
--   Entry (2,1) in nonnegative normalized coordinates.
--
--   Source: https://github.com/alexodas/NewtonianLipschitzOptimality/blob/74f12a8510a4b0087b56f2b309e6ad99fbd26420/NewtonianLipschitz/NormalizedSharpBound.lean#L197-L203
-- source:
--   https://github.com/alexodas/NewtonianLipschitzOptimality/blob/74f12a8510a4b0087b56f2b309e6ad99fbd26420/NewtonianLipschitz/NormalizedSharpBound.lean#L197-L203

module
public import Definitions.Def_NewtonianLipschitz_JacobianMatrix
public import Definitions.Def_NewtonianLipschitz_ScalarMaximum
public import Definitions.Def_NewtonianLipschitz_NormalizedSharpBound
set_option autoImplicit true
@[expose] public section
public section
open NewtonianLipschitz

theorem NewtonianLipschitz.newtonianJacobianMatrix_normalized_two_one
    (μ u v : ℝ) :
    newtonianJacobianMatrix μ (normalizedVector u v) 2 1 =
      (μ / euclideanRadius (normalizedVector u v) ^ 5) *
        (3 * v * u) := by sorry
