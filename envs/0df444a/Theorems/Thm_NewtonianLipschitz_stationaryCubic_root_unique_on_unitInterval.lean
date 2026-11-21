-- Prove2me | Theorems.Thm_NewtonianLipschitz_stationaryCubic_root_unique_on_unitInterval
-- name    : NewtonianLipschitz.stationaryCubic_root_unique_on_unitInterval
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T03:25:41.681179+00:00
-- url     : https://prove2.me/theorems/ef2c014a-de19-461a-8c16-7567dd19ea13
-- title:
--   Newtonian Lipschitz: stationary Cubic root unique on unit Interval
-- statement:
--   There is at most one zero of the polynomial in [0,1].
--   Existence of a zero is a separate intermediate-value obligation.
--
--   Source: https://github.com/alexodas/NewtonianLipschitzOptimality/blob/74f12a8510a4b0087b56f2b309e6ad99fbd26420/NewtonianLipschitz/CubicCandidate.lean#L89-L102
-- source:
--   https://github.com/alexodas/NewtonianLipschitzOptimality/blob/74f12a8510a4b0087b56f2b309e6ad99fbd26420/NewtonianLipschitz/CubicCandidate.lean#L89-L102

module
public import Mathlib
public import Definitions.Def_NewtonianLipschitz_CubicCandidate
set_option autoImplicit true
@[expose] public section
public section
open NewtonianLipschitz

theorem NewtonianLipschitz.stationaryCubic_root_unique_on_unitInterval
    (x y : ℝ)
    (hx : x ∈ Set.Icc (0 : ℝ) 1)
    (hy : y ∈ Set.Icc (0 : ℝ) 1)
    (hpx : stationaryCubic x = 0)
    (hpy : stationaryCubic y = 0) : x = y := by sorry
