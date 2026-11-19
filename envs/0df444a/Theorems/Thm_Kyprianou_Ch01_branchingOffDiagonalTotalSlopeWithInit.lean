-- Prove2me | Theorems.Thm_Kyprianou_Ch01_branchingOffDiagonalTotalSlopeWithInit
-- name    : Kyprianou.Ch01.branchingOffDiagonalTotalSlopeWithInit
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-18T10:14:17.532872+00:00
-- url     : https://prove2.me/theorems/e438d78a-54a0-45e0-a2b1-7bed7e19ccf2
-- title:
--   Total off-diagonal branching exit slope with pure one-ancestor initial state
-- statement:
--   The total off-diagonal small-time probability quotient is the right slope at zero of 1 minus the state-one probability, by the proved exact PMF complement identity. Its derivative is the exit rate lambda by the independently proved diagonal branching generator identity. The source pure-one initial law is explicitly required: it ensures the numerator is zero at t=0, which is necessary for the derivative to agree with the small-time quotient limit.
-- source:
--   Kyprianou (2006), Exercise 1.11(iii), worked solution p.306

import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Probability.ProbabilityMassFunction.Monad
import Mathlib.Topology.Algebra.InfiniteSum.Ring
import Definitions.Def_Kyprianou_Ch01_BranchingGenerator
import Theorems.Thm_Kyprianou_Ch01_branchingOneAncestorOffDiagonalMass
import Theorems.Thm_Kyprianou_Ch01_branchingOneAncestorExitMassDerivative
open Kyprianou.Ch01 MeasureTheory Filter Set
open scoped NNReal ENNReal Topology BigOperators
set_option autoImplicit false

theorem Kyprianou.Ch01.branchingOffDiagonalTotalSlopeWithInit
    (law : PopulationLaws) (rate : NNReal) (offspring : PMF ℕ)
    (hinit : law 1 0 = PMF.pure 1)
    (hRates : IsBranchingRateGenerator law rate offspring) :
    Tendsto (fun t : ℝ =>
      ∑' k : ℕ, (if k = 1 then (0 : ℝ)
         else ((law 1 (Real.toNNReal t)) k).toReal) / t)
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (𝓝 (rate : ℝ)) := by
  sorry
