-- Prove2me | Theorems.Thm_NestedSeatAlloc_IntPolicy_theorem1_one_step_expected_revenue_residual_identity
-- name    : NestedSeatAlloc.IntPolicy.theorem1_one_step_expected_revenue_residual_identity
-- status  : Open
-- author  : @WillR
-- created : 2026-10-08T04:38:23.117277+00:00
-- url     : https://prove2.me/theorems/14a1ae51-a2cc-4539-8dfd-6fe7fdbccdd9
-- title:
--   One-step expected revenue as a residual-capacity integral
-- statement:
--   Expected revenue with k+1 nested fare classes is the next-demand expectation of the current fare earned on the clipped allocation plus the k-class expected revenue at the remaining seats.
-- source:
--   Source-faithful expected-value form of the exact three-branch recursion needed by NestedSeatAlloc.IntPolicy.theorem1_global_optimality_step_all_seats (d9b68cbf-156f-4fa7-a4ac-4abe5f223739). For next demand v, the current-class allocation is min v (max 0 (s-q k)) and the residual capacity is s minus that allocation. Independence of the finite prefix from X(k+1), followed by the finite-prefix law, identifies the inner payoff with expRevenue at the residual. Nonnegativity, measurability and integrability follow from IsSeatModel and the finite fare envelope. This isolates the genuine parameterized Fubini bridge rather than claiming the parent comparison or its separate concavity obligation.

import Mathlib
import Definitions.Def_NestedSeatAlloc_IntPolicy_Model

namespace NestedSeatAlloc.IntPolicy

open MeasureTheory ProbabilityTheory

theorem theorem1_one_step_expected_revenue_residual_identity {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : ℕ → Ω → ℝ) (f q : ℕ → ℝ)
    (hM : IsSeatModel P X f) (hq : IsProtectionPolicy q)
    (k : ℕ) (hk : 1 ≤ k) (s : ℝ) (hs : 0 ≤ s) :
    expRevenue P X f q (k + 1) s =
      ∫ v, f (k + 1) * min v (max 0 (s - q k)) +
        expRevenue P X f q k (s - min v (max 0 (s - q k)))
        ∂Measure.map (X (k + 1)) P := by sorry

end NestedSeatAlloc.IntPolicy
