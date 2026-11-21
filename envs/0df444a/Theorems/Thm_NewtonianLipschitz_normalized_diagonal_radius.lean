-- Prove2me | Theorems.Thm_NewtonianLipschitz_normalized_diagonal_radius
-- name    : NewtonianLipschitz.normalized_diagonal_radius
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T03:36:35.746599+00:00
-- url     : https://prove2.me/theorems/08265e5e-da4b-4249-95c2-0f5ab8a398e4
-- title:
--   Newtonian Lipschitz: normalized diagonal radius
-- statement:
--   The normalized diagonal Euclidean radius coincides with
--   the square-root expression in the candidate denominator.
--
--   Source: https://github.com/alexodas/NewtonianLipschitzOptimality/blob/74f12a8510a4b0087b56f2b309e6ad99fbd26420/NewtonianLipschitz/JacobianSharpWitness.lean#L25-L32
-- source:
--   https://github.com/alexodas/NewtonianLipschitzOptimality/blob/74f12a8510a4b0087b56f2b309e6ad99fbd26420/NewtonianLipschitz/JacobianSharpWitness.lean#L25-L32

module
public import Definitions.Def_NewtonianLipschitz_JacobianOperatorNorm
public import Definitions.Def_NewtonianLipschitz_JacobianSharpWitness
set_option autoImplicit true
@[expose] public section
public section
open NewtonianLipschitz

theorem NewtonianLipschitz.normalized_diagonal_radius (t : ℝ) :
    euclideanRadius (normalizedVector t t) =
      Real.sqrt (1 + 2 * t ^ 2) := by sorry
