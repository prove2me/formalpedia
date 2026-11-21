-- Prove2me | Theorems.Thm_NewtonianLipschitz_stationaryCubic_eq
-- name    : NewtonianLipschitz.stationaryCubic_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T03:22:45.833776+00:00
-- url     : https://prove2.me/theorems/4a4fabd3-d0a1-4990-a98e-4e2c90b7a949
-- title:
--   Newtonian Lipschitz: stationary Cubic eq
-- statement:
--   Exported polynomial formula for downstream proofs.
--
--   Source: https://github.com/alexodas/NewtonianLipschitzOptimality/blob/74f12a8510a4b0087b56f2b309e6ad99fbd26420/NewtonianLipschitz/CubicCandidate.lean#L22-L24
-- source:
--   https://github.com/alexodas/NewtonianLipschitzOptimality/blob/74f12a8510a4b0087b56f2b309e6ad99fbd26420/NewtonianLipschitz/CubicCandidate.lean#L22-L24

module
public import Mathlib
public import Definitions.Def_NewtonianLipschitz_CubicCandidate
set_option autoImplicit true
@[expose] public section
public section
open NewtonianLipschitz

theorem NewtonianLipschitz.stationaryCubic_eq (t : ℝ) :
    stationaryCubic t = 2 * t ^ 3 - 8 * t ^ 2 - 4 * t + 1 := by sorry
