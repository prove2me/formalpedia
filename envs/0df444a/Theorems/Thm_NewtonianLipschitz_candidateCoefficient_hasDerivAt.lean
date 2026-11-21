-- Prove2me | Theorems.Thm_NewtonianLipschitz_candidateCoefficient_hasDerivAt
-- name    : NewtonianLipschitz.candidateCoefficient_hasDerivAt
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T03:31:23.802862+00:00
-- url     : https://prove2.me/theorems/8393f934-e007-41e9-8452-073bd4e50d79
-- title:
--   Newtonian Lipschitz: candidate Coefficient has Deriv At
-- statement:
--   Differentiation of the exact scalar candidate function.
--
--   Source: https://github.com/alexodas/NewtonianLipschitzOptimality/blob/74f12a8510a4b0087b56f2b309e6ad99fbd26420/NewtonianLipschitz/ScalarMaximum.lean#L19-L82
-- source:
--   https://github.com/alexodas/NewtonianLipschitzOptimality/blob/74f12a8510a4b0087b56f2b309e6ad99fbd26420/NewtonianLipschitz/ScalarMaximum.lean#L19-L82

module
public import Definitions.Def_NewtonianLipschitz_CubicCandidate
public import Definitions.Def_NewtonianLipschitz_ScalarMaximum
set_option autoImplicit true
@[expose] public section
public section
open NewtonianLipschitz

theorem NewtonianLipschitz.candidateCoefficient_hasDerivAt (x : ℝ) :
    HasDerivAt candidateCoefficient
      (6 * stationaryCubic x / (Real.sqrt (1 + 2 * x ^ 2)) ^ 7) x := by sorry
