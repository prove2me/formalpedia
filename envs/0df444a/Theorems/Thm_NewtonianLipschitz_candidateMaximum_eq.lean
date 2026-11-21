-- Prove2me | Theorems.Thm_NewtonianLipschitz_candidateMaximum_eq
-- name    : NewtonianLipschitz.candidateMaximum_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T03:20:46.549177+00:00
-- url     : https://prove2.me/theorems/ebe0bb23-b238-431b-9ccf-441bd826ebf0
-- title:
--   Newtonian Lipschitz: candidate Maximum eq
-- statement:
--   Exported equality for the exact scalar maximum across sealed modules.
--
--   Source: https://github.com/alexodas/NewtonianLipschitzOptimality/blob/74f12a8510a4b0087b56f2b309e6ad99fbd26420/NewtonianLipschitz/ScalarMaximum.lean#L151-L153
-- source:
--   https://github.com/alexodas/NewtonianLipschitzOptimality/blob/74f12a8510a4b0087b56f2b309e6ad99fbd26420/NewtonianLipschitz/ScalarMaximum.lean#L151-L153

module
public import Definitions.Def_NewtonianLipschitz_CubicCandidate
public import Definitions.Def_NewtonianLipschitz_ScalarMaximum
set_option autoImplicit true
@[expose] public section
public section
open NewtonianLipschitz

theorem NewtonianLipschitz.candidateMaximum_eq :
    candidateMaximum = candidateCoefficient candidateCriticalPoint := by sorry
