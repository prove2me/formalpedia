-- Prove2me | Theorems.Thm_NewtonianLipschitz_newtonianJacobianMatrix_normalized_two_two
-- name    : NewtonianLipschitz.newtonianJacobianMatrix_normalized_two_two
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T03:29:56.710553+00:00
-- url     : https://prove2.me/theorems/1261f57f-00d2-4196-bc7a-c074550f1396
-- title:
--   Newtonian Lipschitz: newtonian Jacobian Matrix normalized two two
-- statement:
--   Entry (2,2) in nonnegative normalized coordinates.
--
--   Source: https://github.com/alexodas/NewtonianLipschitzOptimality/blob/74f12a8510a4b0087b56f2b309e6ad99fbd26420/NewtonianLipschitz/NormalizedSharpBound.lean#L206-L213
-- source:
--   https://github.com/alexodas/NewtonianLipschitzOptimality/blob/74f12a8510a4b0087b56f2b309e6ad99fbd26420/NewtonianLipschitz/NormalizedSharpBound.lean#L206-L213

module
public import Definitions.Def_NewtonianLipschitz_JacobianMatrix
public import Definitions.Def_NewtonianLipschitz_ScalarMaximum
public import Definitions.Def_NewtonianLipschitz_NormalizedSharpBound
set_option autoImplicit true
@[expose] public section
public section
open NewtonianLipschitz

theorem NewtonianLipschitz.newtonianJacobianMatrix_normalized_two_two
    (μ u v : ℝ) :
    newtonianJacobianMatrix μ (normalizedVector u v) 2 2 =
      (μ / euclideanRadius (normalizedVector u v) ^ 5) *
        (2 * v ^ 2 - 1 - u ^ 2) := by sorry
