-- Prove2me | Theorems.Thm_NewtonianLipschitz_oneSourceGlobalCandidateBound_of_safePlaneFiveFourth
-- name    : NewtonianLipschitz.oneSourceGlobalCandidateBound_of_safePlaneFiveFourth
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T03:50:16.171825+00:00
-- url     : https://prove2.me/theorems/e2ed77aa-1a2b-460e-b01a-602a635aeaab
-- title:
--   Newtonian Lipschitz: one Source Global Candidate Bound of safe Plane Five Fourth
-- statement:
--   The full sharp one-source global C3 statement is a
--   formal consequence of the SINGLE explicit safe-plane
--   5/4 finite-difference proposition. No nonconvex theorem
--   is asserted here without that premise.
--
--   Source: https://github.com/alexodas/NewtonianLipschitzOptimality/blob/74f12a8510a4b0087b56f2b309e6ad99fbd26420/NewtonianLipschitz/SafePlaneReduction.lean#L157-L186
-- source:
--   https://github.com/alexodas/NewtonianLipschitzOptimality/blob/74f12a8510a4b0087b56f2b309e6ad99fbd26420/NewtonianLipschitz/SafePlaneReduction.lean#L157-L186

module
public import Definitions.Def_NewtonianLipschitz_ConditionalFiniteSource
public import Definitions.Def_NewtonianLipschitz_TangentialAlgebra
public import Definitions.Def_NewtonianLipschitz_SafePlaneReduction
set_option autoImplicit true
@[expose] public section
public section
open NewtonianLipschitz

theorem NewtonianLipschitz.oneSourceGlobalCandidateBound_of_safePlaneFiveFourth
    (hPlane : oneSourceSafePlaneFiveFourthBound) :
    oneSourceGlobalCandidateBound := by sorry
