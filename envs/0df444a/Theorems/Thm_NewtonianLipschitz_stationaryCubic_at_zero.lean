-- Prove2me | Theorems.Thm_NewtonianLipschitz_stationaryCubic_at_zero
-- name    : NewtonianLipschitz.stationaryCubic_at_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T03:39:52.693174+00:00
-- url     : https://prove2.me/theorems/04a00fe4-f355-4d9e-a90d-4efba3b09af2
-- title:
--   Newtonian Lipschitz: stationary Cubic at zero
-- statement:
--   The stationary polynomial begins positive on the unit interval.
--
--   Source: https://github.com/alexodas/NewtonianLipschitzOptimality/blob/74f12a8510a4b0087b56f2b309e6ad99fbd26420/NewtonianLipschitz/CubicCandidate.lean#L40-L41
-- source:
--   https://github.com/alexodas/NewtonianLipschitzOptimality/blob/74f12a8510a4b0087b56f2b309e6ad99fbd26420/NewtonianLipschitz/CubicCandidate.lean#L40-L41

module
public import Mathlib
public import Definitions.Def_NewtonianLipschitz_CubicCandidate
set_option autoImplicit true
@[expose] public section
public section
open NewtonianLipschitz

theorem NewtonianLipschitz.stationaryCubic_at_zero : stationaryCubic 0 = 1 := by sorry
