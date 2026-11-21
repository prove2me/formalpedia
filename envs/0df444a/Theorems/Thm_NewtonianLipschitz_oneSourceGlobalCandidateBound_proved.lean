-- Prove2me | Theorems.Thm_NewtonianLipschitz_oneSourceGlobalCandidateBound_proved
-- name    : NewtonianLipschitz.oneSourceGlobalCandidateBound_proved
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T03:53:27.985384+00:00
-- url     : https://prove2.me/theorems/c1f7ea1d-4b01-43f0-9a37-20dc9f386c90
-- title:
--   Newtonian Lipschitz: one Source Global Candidate Bound proved
-- statement:
--   Global C3 finite-difference bound for the exact single-source
--   Newtonian acceleration on the full NONCONVEX exterior of a
--   Cartesian safety cube, without restrictions on the segment
--   between the endpoints. This is unconditional.
--
--   Source: https://github.com/alexodas/NewtonianLipschitzOptimality/blob/74f12a8510a4b0087b56f2b309e6ad99fbd26420/NewtonianLipschitz/SafePlaneFiniteDifference.lean#L122-L125
-- source:
--   https://github.com/alexodas/NewtonianLipschitzOptimality/blob/74f12a8510a4b0087b56f2b309e6ad99fbd26420/NewtonianLipschitz/SafePlaneFiniteDifference.lean#L122-L125

module
public import Definitions.Def_NewtonianLipschitz_PhysicalTangentialAllAxes
public import Definitions.Def_NewtonianLipschitz_SafePlaneFiniteDifference
set_option autoImplicit true
@[expose] public section
public section
open NewtonianLipschitz

theorem NewtonianLipschitz.oneSourceGlobalCandidateBound_proved :
    oneSourceGlobalCandidateBound := by sorry
