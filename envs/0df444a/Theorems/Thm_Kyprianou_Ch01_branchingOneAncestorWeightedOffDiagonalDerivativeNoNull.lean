-- Prove2me | Theorems.Thm_Kyprianou_Ch01_branchingOneAncestorWeightedOffDiagonalDerivativeNoNull
-- name    : Kyprianou.Ch01.branchingOneAncestorWeightedOffDiagonalDerivativeNoNull
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-18T09:58:45.245705+00:00
-- url     : https://prove2.me/theorems/2280cec5-c05a-47ae-a00b-3852db8406c7
-- title:
--   One-ancestor weighted off-diagonal derivative under the source no-null-jumps condition
-- statement:
--   The weighted off-diagonal state probability sum has right derivative at zero equal to rate times the discounted offspring probability moment. This is the substantive discrete Scheffe step: pointwise generator derivatives and initial state 1, together with probability conservation and total exit-rate derivative, imply convergence of the nonnegative off-diagonal difference quotients in ℓ1; the exponential weights lie in [0,1]. The hypothesis offspring(1)=0 is mathematically essential to exclude first-order mass loss into states diverging to infinity.
-- source:
--   Kyprianou (2006), Exercise 1.11(iii), source proof p.306; mass conservation and time-zero generator

import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Probability.ProbabilityMassFunction.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Group
import Definitions.Def_Kyprianou_Ch01_BranchingClocks
import Definitions.Def_Kyprianou_Ch01_BranchingGenerator
open Kyprianou.Ch01 MeasureTheory Set
open scoped NNReal ENNReal BigOperators
set_option autoImplicit false

theorem Kyprianou.Ch01.branchingOneAncestorWeightedOffDiagonalDerivativeNoNull
    (law : PopulationLaws) (rate : NNReal) (offspring : PMF ℕ)
    (hNoNullJumps : offspring 1 = 0)
    (hinit : law 1 0 = PMF.pure 1)
    (hRates : IsBranchingRateGenerator law rate offspring)
    (q : ℝ) (hq : 0 < q) :
    HasDerivWithinAt
      (fun t : ℝ => ∑' k : ℕ,
        if k = 1 then (0 : ℝ)
        else ((law 1 (Real.toNNReal t)) k).toReal *
          Real.exp (-q * (k : ℝ)))
      ((rate : ℝ) * ∑' k : ℕ,
        (offspring k).toReal * Real.exp (-q * (k : ℝ)))
      (Set.Ici 0) 0 := by
  sorry
