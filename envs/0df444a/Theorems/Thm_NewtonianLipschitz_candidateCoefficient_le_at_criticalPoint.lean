-- Prove2me | Theorems.Thm_NewtonianLipschitz_candidateCoefficient_le_at_criticalPoint
-- name    : NewtonianLipschitz.candidateCoefficient_le_at_criticalPoint
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T03:21:00.739036+00:00
-- url     : https://prove2.me/theorems/2385f085-003b-4887-8d40-df738f1fc32e
-- title:
--   Newtonian Lipschitz: candidate Coefficient le at critical Point
-- statement:
--   The exact cubic root realizes the maximum of the candidate scalar
--   coefficient on the unit interval. The separate R024–R027
--   results obtain the physical Cartesian Jacobian and operator
--   bounds from this scalar ingredient.
--
--   Source: https://github.com/alexodas/NewtonianLipschitzOptimality/blob/74f12a8510a4b0087b56f2b309e6ad99fbd26420/NewtonianLipschitz/ScalarMaximum.lean#L114-L144
-- source:
--   https://github.com/alexodas/NewtonianLipschitzOptimality/blob/74f12a8510a4b0087b56f2b309e6ad99fbd26420/NewtonianLipschitz/ScalarMaximum.lean#L114-L144

module
public import Definitions.Def_NewtonianLipschitz_CubicCandidate
public import Definitions.Def_NewtonianLipschitz_ScalarMaximum
set_option autoImplicit true
@[expose] public section
public section
open NewtonianLipschitz

theorem NewtonianLipschitz.candidateCoefficient_le_at_criticalPoint
    (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    candidateCoefficient t ≤
      candidateCoefficient candidateCriticalPoint := by sorry
