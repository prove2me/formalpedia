-- Prove2me | Theorems.Thm_NewtonianLipschitz_newtonianJacobianMatrix_normalized_one_one
-- name    : NewtonianLipschitz.newtonianJacobianMatrix_normalized_one_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T03:29:44.812044+00:00
-- url     : https://prove2.me/theorems/e9acdc0c-a30c-4126-936d-03a220a45fa0
-- title:
--   Newtonian Lipschitz: newtonian Jacobian Matrix normalized one one
-- statement:
--   Exact diagonal entry in the second row.
--
--   Source: https://github.com/alexodas/NewtonianLipschitzOptimality/blob/74f12a8510a4b0087b56f2b309e6ad99fbd26420/NewtonianLipschitz/NormalizedSharpBound.lean#L104-L111
-- source:
--   https://github.com/alexodas/NewtonianLipschitzOptimality/blob/74f12a8510a4b0087b56f2b309e6ad99fbd26420/NewtonianLipschitz/NormalizedSharpBound.lean#L104-L111

module
public import Definitions.Def_NewtonianLipschitz_JacobianMatrix
public import Definitions.Def_NewtonianLipschitz_ScalarMaximum
public import Definitions.Def_NewtonianLipschitz_NormalizedSharpBound
set_option autoImplicit true
@[expose] public section
public section
open NewtonianLipschitz

theorem NewtonianLipschitz.newtonianJacobianMatrix_normalized_one_one
    (μ u v : ℝ) :
    newtonianJacobianMatrix μ (normalizedVector u v) 1 1 =
      (μ / euclideanRadius (normalizedVector u v) ^ 5) *
        (2 * u ^ 2 - 1 - v ^ 2) := by sorry
