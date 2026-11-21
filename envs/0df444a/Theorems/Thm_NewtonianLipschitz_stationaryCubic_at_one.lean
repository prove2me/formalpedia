-- Prove2me | Theorems.Thm_NewtonianLipschitz_stationaryCubic_at_one
-- name    : NewtonianLipschitz.stationaryCubic_at_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T03:40:23.446113+00:00
-- url     : https://prove2.me/theorems/6ce9cb32-7079-4512-a0ad-602dcfb30e66
-- title:
--   Newtonian Lipschitz: stationary Cubic at one
-- statement:
--   The stationary polynomial ends negative on the unit interval.
--
--   Source: https://github.com/alexodas/NewtonianLipschitzOptimality/blob/74f12a8510a4b0087b56f2b309e6ad99fbd26420/NewtonianLipschitz/CubicCandidate.lean#L44-L45
-- source:
--   https://github.com/alexodas/NewtonianLipschitzOptimality/blob/74f12a8510a4b0087b56f2b309e6ad99fbd26420/NewtonianLipschitz/CubicCandidate.lean#L44-L45

module
public import Mathlib
public import Definitions.Def_NewtonianLipschitz_CubicCandidate
set_option autoImplicit true
@[expose] public section
public section
open NewtonianLipschitz

theorem NewtonianLipschitz.stationaryCubic_at_one : stationaryCubic 1 = -9 := by sorry
