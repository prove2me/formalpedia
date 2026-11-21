-- Prove2me | Theorems.Thm_NewtonianLipschitz_normalizedVector_radius_eq_diagonal
-- name    : NewtonianLipschitz.normalizedVector_radius_eq_diagonal
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T03:32:54.613532+00:00
-- url     : https://prove2.me/theorems/5931cdf2-f62c-4b65-8796-c8a933aa57ce
-- title:
--   Newtonian Lipschitz: normalized Vector radius eq diagonal
-- statement:
--   The normalized Euclidean radius depends only on the diagonal
--   parameter constructed from the two smaller coordinates.
--
--   Source: https://github.com/alexodas/NewtonianLipschitzOptimality/blob/74f12a8510a4b0087b56f2b309e6ad99fbd26420/NewtonianLipschitz/NormalizedSharpBound.lean#L36-L46
-- source:
--   https://github.com/alexodas/NewtonianLipschitzOptimality/blob/74f12a8510a4b0087b56f2b309e6ad99fbd26420/NewtonianLipschitz/NormalizedSharpBound.lean#L36-L46

module
public import Definitions.Def_NewtonianLipschitz_JacobianMatrix
public import Definitions.Def_NewtonianLipschitz_ScalarMaximum
public import Definitions.Def_NewtonianLipschitz_NormalizedSharpBound
set_option autoImplicit true
@[expose] public section
public section
open NewtonianLipschitz

theorem NewtonianLipschitz.normalizedVector_radius_eq_diagonal
    (u v : ℝ) :
    euclideanRadius (normalizedVector u v) =
      Real.sqrt (1 + 2 * (diagonalParameter u v) ^ 2) := by sorry
