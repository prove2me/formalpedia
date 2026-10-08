-- Prove2me | Theorems.Thm_NestedSeatAlloc_IntPolicy_conditionalRevenue_succ_expected_piecewise_prob
-- name    : NestedSeatAlloc.IntPolicy.conditionalRevenue_succ_expected_piecewise_prob
-- status  : Open
-- author  : @WillR
-- created : 2026-10-08T03:45:57.056982+00:00
-- url     : https://prove2.me/theorems/8f39e977-ede7-449c-99b4-7daca1276c25
-- title:
--   Frozen next-demand recursion uses unconditional prefix expectation
-- statement:
--   Under the probability seat model, freezing demand of class k+1 at y gives a three-region recursion whose lower-level terms are the unconditional expected revenue through class k, because the lower recursion does not read the frozen coordinate.
-- source:
--   Exact recursion in Definitions.Def_NestedSeatAlloc_IntPolicy_Model: condRevenue at level k+1 overwrites X(k+1), and revenue at level k depends only on demand coordinates through k. Unfolding the three branches and reducing the level-k integrals gives the displayed identity; IsSeatModel supplies that P is a probability measure, needed to integrate the constant fare terms. This corrected identity supports the fixed-demand concavity proof for corollary1_conditional_revenue_concave (e5c4f26f-0565-4b78-9161-3b3ae9b93077); it does not itself prove concavity.

import Mathlib
import Definitions.Def_NestedSeatAlloc_IntPolicy_Model

open MeasureTheory ProbabilityTheory
open NestedSeatAlloc.IntPolicy

namespace NestedSeatAlloc.IntPolicy

open MeasureTheory ProbabilityTheory

theorem conditionalRevenue_succ_expected_piecewise_prob
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : ℕ → Ω → ℝ) (f p : ℕ → ℝ)
    (hM : IsSeatModel P X f) (k : ℕ) (hk : 1 ≤ k) (y s : ℝ) :
    condRevenue P X f p (k + 1) y s =
      (if s < p k then expRevenue P X f p k s
       else if s < p k + y then
         (s - p k) * f (k + 1) + expRevenue P X f p k (p k)
       else y * f (k + 1) + expRevenue P X f p k (s - y)) := by sorry

end NestedSeatAlloc.IntPolicy
