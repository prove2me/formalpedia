-- Prove2me | Theorems.Thm_NestedSeatAlloc_IntPolicy_conditionalRevenue_succ_expected_piecewise
-- name    : NestedSeatAlloc.IntPolicy.conditionalRevenue_succ_expected_piecewise
-- status  : Open
-- author  : @WillR
-- created : 2026-10-08T03:45:01.49645+00:00
-- url     : https://prove2.me/theorems/f1f174de-0dc7-404e-996e-8667e9d5e5c9
-- title:
--   Frozen next-demand recursion uses unconditional prefix revenue
-- statement:
--   When the demand of class k+1 is frozen at y, the three-region expected-revenue recursion uses the unconditional expected revenue through class k in each lower branch, because the lower recursion does not read the frozen coordinate.
-- source:
--   Exact recursion in Definitions.Def_NestedSeatAlloc_IntPolicy_Model: condRevenue at level k+1 overwrites X(k+1), and revenue at level k depends only on demand coordinates through k. Unfolding the three branches and reducing the level-k integrals gives the displayed identity. This corrects the frozen-index mismatch in the separately published Open conditionalRevenue_succ_piecewise statement and supplies the model identity needed by the fixed-demand concavity proof for corollary1_conditional_revenue_concave (e5c4f26f-0565-4b78-9161-3b3ae9b93077); it does not itself prove concavity.

import Mathlib
import Definitions.Def_NestedSeatAlloc_IntPolicy_Model

open MeasureTheory ProbabilityTheory
open NestedSeatAlloc.IntPolicy

namespace NestedSeatAlloc.IntPolicy

open MeasureTheory ProbabilityTheory

theorem conditionalRevenue_succ_expected_piecewise
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : ℕ → Ω → ℝ) (f p : ℕ → ℝ)
    (k : ℕ) (hk : 1 ≤ k) (y s : ℝ) :
    condRevenue P X f p (k + 1) y s =
      (if s < p k then expRevenue P X f p k s
       else if s < p k + y then
         (s - p k) * f (k + 1) + expRevenue P X f p k (p k)
       else y * f (k + 1) + expRevenue P X f p k (s - y)) := by sorry

end NestedSeatAlloc.IntPolicy
