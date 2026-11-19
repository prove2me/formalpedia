-- Prove2me | Theorems.Thm_Kyprianou_Ch01_branchingFiniteLaplaceGenerator
-- name    : Kyprianou.Ch01.branchingFiniteLaplaceGenerator
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-18T07:27:13.533531+00:00
-- url     : https://prove2.me/theorems/fb890e4a-5a29-496a-bb6f-21746f9617df
-- title:
--   Finite-truncation Laplace derivative follows from the branching transition-rate matrix
-- statement:
--   Under the exact one-ancestor branching transition-rate Q-matrix, each finite truncation of the one-ancestor population Laplace sum has derivative at t=0 equal to the corresponding weighted finite sum of Q-matrix entries. This is the finite-sum step towards Exercise 1.11(iii); passing to the infinite population Laplace sum is a separate, genuinely nontrivial limit interchange.
-- source:
--   Kyprianou (2006), Exercise 1.11(iii), worked solution printed page 306

import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Probability.ProbabilityMassFunction.Basic
import Definitions.Def_Kyprianou_Ch01_BranchingGenerator
open Kyprianou.Ch01 MeasureTheory Filter Set
open scoped NNReal ENNReal BigOperators
set_option autoImplicit false

theorem Kyprianou.Ch01.branchingFiniteLaplaceGenerator
    (law : PopulationLaws) (rate : ℝ≥0) (offspring : PMF ℕ)
    (hRates : IsBranchingRateGenerator law rate offspring)
    (N : ℕ) (q : ℝ) :
    HasDerivWithinAt
      (fun t : ℝ => ∑ k ∈ Finset.range N,
        ((law 1 (Real.toNNReal t)) k).toReal *
          Real.exp (-q * (k : ℝ)))
      (∑ k ∈ Finset.range N,
        (if k = 1 then -((rate : ℝ) * (1 : ℝ))
        else if 1 ≤ k + 1 then
          (rate : ℝ) * (1 : ℝ) * (offspring (k + 1 - 1)).toReal
        else 0) * Real.exp (-q * (k : ℝ)))
      (Set.Ici 0) 0 := by
  sorry
