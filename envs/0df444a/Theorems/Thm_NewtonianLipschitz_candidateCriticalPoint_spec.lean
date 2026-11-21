-- Prove2me | Theorems.Thm_NewtonianLipschitz_candidateCriticalPoint_spec
-- name    : NewtonianLipschitz.candidateCriticalPoint_spec
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T03:20:46.697277+00:00
-- url     : https://prove2.me/theorems/10c4ff29-eded-432e-969e-206974453bf7
-- title:
--   Newtonian Lipschitz: candidate Critical Point spec
-- statement:
--   Exact enclosure and stationary polynomial equation.
--
--   Source: https://github.com/alexodas/NewtonianLipschitzOptimality/blob/74f12a8510a4b0087b56f2b309e6ad99fbd26420/NewtonianLipschitz/CubicCandidate.lean#L148-L152
-- source:
--   https://github.com/alexodas/NewtonianLipschitzOptimality/blob/74f12a8510a4b0087b56f2b309e6ad99fbd26420/NewtonianLipschitz/CubicCandidate.lean#L148-L152

module
public import Mathlib
public import Definitions.Def_NewtonianLipschitz_CubicCandidate
set_option autoImplicit true
@[expose] public section
public section
open NewtonianLipschitz

theorem NewtonianLipschitz.candidateCriticalPoint_spec :
    (9 / 50 : ℝ) ≤ candidateCriticalPoint ∧
      candidateCriticalPoint ≤ 1 / 5 ∧
      stationaryCubic candidateCriticalPoint = 0 := by sorry
