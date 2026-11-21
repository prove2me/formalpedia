-- Prove2me | Theorems.Thm_NewtonianLipschitz_stationaryCubic_negative_after_root
-- name    : NewtonianLipschitz.stationaryCubic_negative_after_root
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T03:31:43.860698+00:00
-- url     : https://prove2.me/theorems/2d52e852-6729-41ff-931f-4e9dd993f86b
-- title:
--   Newtonian Lipschitz: stationary Cubic negative after root
-- statement:
--   The stationary cubic is negative to the right of the exact root.
--
--   Source: https://github.com/alexodas/NewtonianLipschitzOptimality/blob/74f12a8510a4b0087b56f2b309e6ad99fbd26420/NewtonianLipschitz/ScalarMaximum.lean#L98-L108
-- source:
--   https://github.com/alexodas/NewtonianLipschitzOptimality/blob/74f12a8510a4b0087b56f2b309e6ad99fbd26420/NewtonianLipschitz/ScalarMaximum.lean#L98-L108

module
public import Definitions.Def_NewtonianLipschitz_CubicCandidate
public import Definitions.Def_NewtonianLipschitz_ScalarMaximum
set_option autoImplicit true
@[expose] public section
public section
open NewtonianLipschitz

theorem NewtonianLipschitz.stationaryCubic_negative_after_root
    (x : ℝ) (hxa : candidateCriticalPoint < x) (hx1 : x ≤ 1) :
    stationaryCubic x < 0 := by sorry
