-- Prove2me | Theorems.Thm_NewtonianLipschitz_stationaryCubic_strictAntiOn_unitInterval
-- name    : NewtonianLipschitz.stationaryCubic_strictAntiOn_unitInterval
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T03:25:35.62741+00:00
-- url     : https://prove2.me/theorems/fda1d13c-6b78-4b86-befd-ce426fa3f082
-- title:
--   Newtonian Lipschitz: stationary Cubic strict Anti On unit Interval
-- statement:
--   The candidate stationary polynomial is strictly decreasing on [0,1].
--
--   Source: https://github.com/alexodas/NewtonianLipschitzOptimality/blob/74f12a8510a4b0087b56f2b309e6ad99fbd26420/NewtonianLipschitz/CubicCandidate.lean#L58-L85
-- source:
--   https://github.com/alexodas/NewtonianLipschitzOptimality/blob/74f12a8510a4b0087b56f2b309e6ad99fbd26420/NewtonianLipschitz/CubicCandidate.lean#L58-L85

module
public import Mathlib
public import Definitions.Def_NewtonianLipschitz_CubicCandidate
set_option autoImplicit true
@[expose] public section
public section
open NewtonianLipschitz

theorem NewtonianLipschitz.stationaryCubic_strictAntiOn_unitInterval :
    StrictAntiOn stationaryCubic (Set.Icc (0 : ℝ) 1) := by sorry
