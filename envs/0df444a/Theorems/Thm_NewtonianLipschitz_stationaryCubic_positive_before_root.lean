-- Prove2me | Theorems.Thm_NewtonianLipschitz_stationaryCubic_positive_before_root
-- name    : NewtonianLipschitz.stationaryCubic_positive_before_root
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T03:31:37.071592+00:00
-- url     : https://prove2.me/theorems/8148a6c6-4c12-489c-b520-96befe675baf
-- title:
--   Newtonian Lipschitz: stationary Cubic positive before root
-- statement:
--   The stationary cubic is positive to the left of the exact root.
--
--   Source: https://github.com/alexodas/NewtonianLipschitzOptimality/blob/74f12a8510a4b0087b56f2b309e6ad99fbd26420/NewtonianLipschitz/ScalarMaximum.lean#L85-L95
-- source:
--   https://github.com/alexodas/NewtonianLipschitzOptimality/blob/74f12a8510a4b0087b56f2b309e6ad99fbd26420/NewtonianLipschitz/ScalarMaximum.lean#L85-L95

module
public import Definitions.Def_NewtonianLipschitz_CubicCandidate
public import Definitions.Def_NewtonianLipschitz_ScalarMaximum
set_option autoImplicit true
@[expose] public section
public section
open NewtonianLipschitz

theorem NewtonianLipschitz.stationaryCubic_positive_before_root
    (x : ℝ) (hx0 : 0 ≤ x) (hxa : x < candidateCriticalPoint) :
    0 < stationaryCubic x := by sorry
