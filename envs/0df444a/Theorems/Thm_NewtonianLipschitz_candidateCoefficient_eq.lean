-- Prove2me | Theorems.Thm_NewtonianLipschitz_candidateCoefficient_eq
-- name    : NewtonianLipschitz.candidateCoefficient_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T03:20:18.968695+00:00
-- url     : https://prove2.me/theorems/c89b441f-2e39-40c1-9ca9-360c78f5e83d
-- title:
--   Newtonian Lipschitz: candidate Coefficient eq
-- statement:
--   Exported exact coefficient formula for downstream proofs.
--
--   Source: https://github.com/alexodas/NewtonianLipschitzOptimality/blob/74f12a8510a4b0087b56f2b309e6ad99fbd26420/NewtonianLipschitz/CubicCandidate.lean#L31-L35
-- source:
--   https://github.com/alexodas/NewtonianLipschitzOptimality/blob/74f12a8510a4b0087b56f2b309e6ad99fbd26420/NewtonianLipschitz/CubicCandidate.lean#L31-L35

module
public import Mathlib
public import Definitions.Def_NewtonianLipschitz_CubicCandidate
set_option autoImplicit true
@[expose] public section
public section
open NewtonianLipschitz

theorem NewtonianLipschitz.candidateCoefficient_eq (t : ℝ) :
    candidateCoefficient t =
      (2 + 6 * t - 2 * t ^ 2) /
        (Real.sqrt (1 + 2 * t ^ 2)) ^ 5 := by sorry
