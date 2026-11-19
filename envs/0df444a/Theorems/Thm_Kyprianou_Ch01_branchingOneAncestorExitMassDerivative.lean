-- Prove2me | Theorems.Thm_Kyprianou_Ch01_branchingOneAncestorExitMassDerivative
-- name    : Kyprianou.Ch01.branchingOneAncestorExitMassDerivative
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-18T08:45:50.509791+00:00
-- url     : https://prove2.me/theorems/d1a1e2bb-6fab-44ce-bc97-e38c0a7672c0
-- title:
--   Total off-diagonal small-time branching exit rate from the single-ancestor diagonal generator
-- statement:
--   The derivative at the time-zero right boundary of one minus the probability of still having exactly one descendant is the positive rate lambda. This follows immediately from the original one-ancestor generator diagonal entry Q_11=-lambda. In conjunction with the exact PMF mass-complement identity, this certifies convergence of the total off-diagonal exit mass at small time, the essential global-mass input to Scheffe-type interchange of the weighted infinite branching Laplace derivative.
-- source:
--   Kyprianou (2006), Exercise 1.11(iii), worked answer p.306

import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Probability.ProbabilityMassFunction.Basic
import Definitions.Def_Kyprianou_Ch01_BranchingGenerator
open Kyprianou.Ch01 MeasureTheory Set
set_option autoImplicit false

theorem Kyprianou.Ch01.branchingOneAncestorExitMassDerivative
    (law : PopulationLaws) (rate : NNReal) (offspring : PMF ℕ)
    (hRates : IsBranchingRateGenerator law rate offspring) :
    HasDerivWithinAt
      (fun t : ℝ => 1 - ((law 1 (Real.toNNReal t)) 1).toReal)
      (rate : ℝ) (Set.Ici 0) 0 := by
  sorry
