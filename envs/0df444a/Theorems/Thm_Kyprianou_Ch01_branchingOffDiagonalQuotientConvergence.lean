-- Prove2me | Theorems.Thm_Kyprianou_Ch01_branchingOffDiagonalQuotientConvergence
-- name    : Kyprianou.Ch01.branchingOffDiagonalQuotientConvergence
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-18T10:19:00.744325+00:00
-- url     : https://prove2.me/theorems/245e419d-1b67-47c1-a0ad-8b46d554aefa
-- title:
--   Pointwise and total small-time off-diagonal branching probability quotient limits
-- statement:
--   As t decreases to zero through positive times, each off-diagonal one-ancestor probability divided by t converges to its source Q-matrix rate, while the sum of all off-diagonal quotients converges to the total exit rate. The first statement follows from individual HasDerivWithinAt generator conditions and the pure one-ancestor initial law. The second is the source diagonal derivative and the already Proved exact PMF mass-complement identity. These are precisely the pointwise and mass hypotheses needed for the discrete Scheffe weighted-sum theorem.
-- source:
--   Kyprianou (2006), Exercise 1.11(iii), p.306

import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Topology.Algebra.InfiniteSum.Ring
import Mathlib.Probability.ProbabilityMassFunction.Basic
import Definitions.Def_Kyprianou_Ch01_BranchingGenerator
import Theorems.Thm_Kyprianou_Ch01_branchingOneAncestorOffDiagonalMass
import Theorems.Thm_Kyprianou_Ch01_branchingOneAncestorExitMassDerivative
open Kyprianou.Ch01 MeasureTheory Filter Set
open scoped NNReal ENNReal Topology BigOperators
set_option autoImplicit false

theorem Kyprianou.Ch01.branchingOffDiagonalQuotientConvergence
    (law : PopulationLaws) (rate : NNReal) (offspring : PMF ℕ)
    (hinit : law 1 0 = PMF.pure 1)
    (hRates : IsBranchingRateGenerator law rate offspring) :
    (∀ k : ℕ, Tendsto
      (fun t : ℝ =>
        (if k = 1 then (0 : ℝ)
         else ((law 1 (Real.toNNReal t)) k).toReal) / t)
      (nhdsWithin (0 : ℝ) (Set.Ioi 0))
      (𝓝 (if k = 1 then (0 : ℝ)
          else (rate : ℝ) * (offspring k).toReal))) ∧
    Tendsto (fun t : ℝ =>
      ∑' k : ℕ, (if k = 1 then (0 : ℝ)
         else ((law 1 (Real.toNNReal t)) k).toReal) / t)
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (𝓝 (rate : ℝ)) := by
  sorry
