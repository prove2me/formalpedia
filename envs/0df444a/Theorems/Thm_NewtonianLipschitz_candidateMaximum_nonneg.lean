-- Prove2me | Theorems.Thm_NewtonianLipschitz_candidateMaximum_nonneg
-- name    : NewtonianLipschitz.candidateMaximum_nonneg
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T03:31:34.078172+00:00
-- url     : https://prove2.me/theorems/c24b1244-e063-44d9-b8ad-e77ecb166434
-- title:
--   Newtonian Lipschitz: candidate Maximum nonneg
-- statement:
--   The exact scalar candidate maximum is nonnegative.
--   It is at least the value 2 attained at parameter zero.
--
--   Source: https://github.com/alexodas/NewtonianLipschitzOptimality/blob/74f12a8510a4b0087b56f2b309e6ad99fbd26420/NewtonianLipschitz/JacobianCartesianBound.lean#L45-L55
-- source:
--   https://github.com/alexodas/NewtonianLipschitzOptimality/blob/74f12a8510a4b0087b56f2b309e6ad99fbd26420/NewtonianLipschitz/JacobianCartesianBound.lean#L45-L55

module
public import Definitions.Def_NewtonianLipschitz_JacobianSignedBounds
public import Definitions.Def_NewtonianLipschitz_JacobianCartesianBound
set_option autoImplicit true
@[expose] public section
public section
open NewtonianLipschitz

theorem NewtonianLipschitz.candidateMaximum_nonneg : 0 ≤ candidateMaximum := by sorry
