-- Prove2me | Theorems.Thm_Kyprianou_Ch01_branchingOneAncestorInfiniteDerivative
-- name    : Kyprianou.Ch01.branchingOneAncestorInfiniteDerivative
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-18T08:27:56.981125+00:00
-- url     : https://prove2.me/theorems/6d9a6197-5ac3-4746-9c2a-cba76b1ce728
-- title:
--   One-ancestor branching InfiniteDerivative
-- statement:
--   The initial one-ancestor branching population is concentrated at state one. Under its specified pointwise transition generator, identify the full derivative of its Laplace transform at the origin by passing from finite truncation derivatives to the infinite weighted Q-row sum. This nontrivial interchange can be justified by conservation of probability mass, the one-ancestor diagonal derivative and nonnegative off-diagonal transition rates. It is independent of the final offspring-mechanism simplification.
-- source:
--   Kyprianou (2006), Exercise 1.11(iii), worked answer printed page 306

import Mathlib.Probability.ProbabilityMassFunction.Basic
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Topology.Algebra.InfiniteSum.Group
import Definitions.Def_Kyprianou_Ch01_BranchingClocks
import Definitions.Def_Kyprianou_Ch01_BranchingGenerator
open Kyprianou.Ch01 MeasureTheory Set
open scoped NNReal ENNReal BigOperators
set_option autoImplicit false

theorem Kyprianou.Ch01.branchingOneAncestorInfiniteDerivative
    (law : PopulationLaws) (rate : ℝ≥0) (offspring : PMF ℕ)
    (hrate : 0 < rate) (hNoNullJumps : offspring 1 = 0)
    (hinit : law 1 0 = PMF.pure 1)
    (hRates : IsBranchingRateGenerator law rate offspring)
    (q : ℝ) (hq : 0 < q) :
    HasDerivWithinAt
      (fun t : ℝ => branchingLaplace law 1 (Real.toNNReal t) q)
      (∑' k : ℕ,
        (if k = 1 then -(rate : ℝ)
         else (rate : ℝ) * (offspring k).toReal) *
        Real.exp (-q * (k : ℝ)))
      (Set.Ici 0) 0 := by
  sorry
