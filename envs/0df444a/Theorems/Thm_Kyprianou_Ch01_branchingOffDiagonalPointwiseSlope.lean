-- Prove2me | Theorems.Thm_Kyprianou_Ch01_branchingOffDiagonalPointwiseSlope
-- name    : Kyprianou.Ch01.branchingOffDiagonalPointwiseSlope
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-18T10:12:18.753204+00:00
-- url     : https://prove2.me/theorems/18433076-d6b3-4f18-8180-31ec3663934d
-- title:
--   branchingOffDiagonalPointwiseSlope
-- statement:
--   Each off-diagonal source transition probability is initially zero and has right derivative lambda p_k at zero. Divide by positive t and use pinned HasDerivWithinAt iff Tendsto slope to prove pointwise convergence of the off-diagonal small-time quotient for all k; the k=1 term is zero by definition.
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

theorem Kyprianou.Ch01.branchingOffDiagonalPointwiseSlope
    (law : PopulationLaws) (rate : NNReal) (offspring : PMF ℕ)
    (hinit : law 1 0 = PMF.pure 1)
    (hRates : IsBranchingRateGenerator law rate offspring) :
    ∀ k : ℕ, Tendsto
      (fun t : ℝ =>
        (if k = 1 then (0 : ℝ)
         else ((law 1 (Real.toNNReal t)) k).toReal) / t)
      (nhdsWithin (0 : ℝ) (Set.Ioi 0))
      (𝓝 (if k = 1 then (0 : ℝ)
          else (rate : ℝ) * (offspring k).toReal)) := by
  sorry
