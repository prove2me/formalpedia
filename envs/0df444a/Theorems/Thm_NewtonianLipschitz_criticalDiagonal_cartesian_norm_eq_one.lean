-- Prove2me | Theorems.Thm_NewtonianLipschitz_criticalDiagonal_cartesian_norm_eq_one
-- name    : NewtonianLipschitz.criticalDiagonal_cartesian_norm_eq_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T03:34:50.517487+00:00
-- url     : https://prove2.me/theorems/eb6c0687-7eb7-4cc6-9418-dec191626ba2
-- title:
--   Newtonian Lipschitz: critical Diagonal cartesian norm eq one
-- statement:
--   The critical diagonal displacement has Cartesian norm one.
--
--   Source: https://github.com/alexodas/NewtonianLipschitzOptimality/blob/74f12a8510a4b0087b56f2b309e6ad99fbd26420/NewtonianLipschitz/JacobianSharpWitness.lean#L54-L63
-- source:
--   https://github.com/alexodas/NewtonianLipschitzOptimality/blob/74f12a8510a4b0087b56f2b309e6ad99fbd26420/NewtonianLipschitz/JacobianSharpWitness.lean#L54-L63

module
public import Definitions.Def_NewtonianLipschitz_JacobianOperatorNorm
public import Definitions.Def_NewtonianLipschitz_JacobianSharpWitness
set_option autoImplicit true
@[expose] public section
public section
open NewtonianLipschitz

theorem NewtonianLipschitz.criticalDiagonal_cartesian_norm_eq_one :
    ‖normalizedVector candidateCriticalPoint candidateCriticalPoint‖ =
      (1 : ℝ) := by sorry
