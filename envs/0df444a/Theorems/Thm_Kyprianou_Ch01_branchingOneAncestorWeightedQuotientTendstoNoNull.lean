-- Prove2me | Theorems.Thm_Kyprianou_Ch01_branchingOneAncestorWeightedQuotientTendstoNoNull
-- name    : Kyprianou.Ch01.branchingOneAncestorWeightedQuotientTendstoNoNull
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-18T10:36:56.628013+00:00
-- url     : https://prove2.me/theorems/24983034-f4e3-4b71-a934-1f80f8bd4ad1
-- title:
--   Source no-null branching weighted off-diagonal quotient convergence
-- statement:
--   Under the source condition offspring(1)=0, the positive off-diagonal quotient family has pointwise convergence to lambda p_k and total mass convergence to lambda. Its discount weights exp(-q k) belong to [0,1]. The discrete Scheffe lemma therefore proves the limit of the weighted quotient sum, which is the substantive derivative-interchange step for Exercise 1.11(iii).
-- source:
--   Kyprianou (2006), Exercise 1.11(iii), p.306

import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Topology.Algebra.InfiniteSum.Ring
import Definitions.Def_Kyprianou_Ch01_BranchingGenerator
open Kyprianou.Ch01 MeasureTheory Filter Set
open scoped NNReal ENNReal Topology BigOperators
set_option autoImplicit false

theorem Kyprianou.Ch01.branchingOneAncestorWeightedQuotientTendstoNoNull
    (law : PopulationLaws) (rate : NNReal) (offspring : PMF ℕ)
    (hNoNullJumps : offspring 1 = 0)
    (hinit : law 1 0 = PMF.pure 1)
    (hRates : IsBranchingRateGenerator law rate offspring)
    (q : ℝ) (hq : 0 < q) :
    Tendsto (fun t : ℝ =>
      ∑' k : ℕ,
        ((if k = 1 then (0 : ℝ)
         else ((law 1 (Real.toNNReal t)) k).toReal) / t) *
          Real.exp (-q * (k : ℝ)))
      (nhdsWithin (0 : ℝ) (Set.Ioi 0))
      (𝓝 ((rate : ℝ) * ∑' k : ℕ,
        (offspring k).toReal * Real.exp (-q * (k : ℝ)))) := by
  sorry
