-- Prove2me | Theorems.Thm_NestedSeatAlloc_IntPolicy_all_prefixes_clbi_of_integer_subdiff
-- name    : NestedSeatAlloc.IntPolicy.all_prefixes_clbi_of_integer_subdiff
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-08T13:38:30.374679+00:00
-- url     : https://prove2.me/theorems/c1bdc52e-9229-4342-9e26-c11f7f920cc0
-- title:
--   All expected-revenue prefixes are CLBI for an integer policy satisfying the subdifferential conditions
-- statement:
--   # CLBI at every depth for an integer policy satisfying condition (20)
--
--   Fix a model with nonnegative integer-valued demands, positive fares and an
--   integer protection-level policy p that satisfies all the subdifferential
--   conditions of Theorem 2.
--
--   The Proved eq27_er1_clbi theorem establishes CLBI of expected revenue at
--   depth 1, independently of the protection levels. For depth k+1, the Proved
--   clbi_propagation theorem takes CLBI of ER_k and the instances of condition
--   (20) for the prefix 1..k, and concludes CLBI of ER_(k+1). The global
--   SubdiffCondition assumption supplies these prefix instances. Natural-number
--   induction establishes CLBI of ER_k for every k>=1.
--
--   The CLBI predicate includes concavity on nonnegative capacities. This
--   result supplies the concavity hypothesis needed by
--   conditional_optimality_with_concavity when the chosen policy comes from the
--   already Proved theorem2_integer_subdiff_policy_exists. It avoids an
--   unjustified concavity deduction from the weaker general Theorem 1 optimality
--   hypothesis and is specific to the integer-demand theorem.
--
--   The candidate is a sound mathematical reduction to existing Proved
--   results. Lean source must be checked by the remote Prove2Me compiler.
-- source:
--   # CLBI at every depth for an integer policy satisfying condition (20)
--
--   Fix a model with nonnegative integer-valued demands, positive fares and an
--   integer protection-level policy p that satisfies all the subdifferential
--   conditions of Theorem 2.
--
--   The Proved eq27_er1_clbi theorem establishes CLBI of expected revenue at
--   depth 1, independently of the protection levels. For depth k+1, the Proved
--   clbi_propagation theorem takes CLBI of ER_k and the instances of condition
--   (20) for the prefix 1..k, and concludes CLBI of ER_(k+1). The global
--   SubdiffCondition assumption supplies these prefix instances. Natural-number
--   induction establishes CLBI of ER_k for every k>=1.
--
--   The CLBI predicate includes concavity on nonnegative capacities. This
--   result supplies the concavity hypothesis needed by
--   conditional_optimality_with_concavity when the chosen policy comes from the
--   already Proved theorem2_integer_subdiff_policy_exists. It avoids an
--   unjustified concavity deduction from the weaker general Theorem 1 optimality
--   hypothesis and is specific to the integer-demand theorem.
--
--   The candidate is a sound mathematical reduction to existing Proved
--   results. Lean source must be checked by the remote Prove2Me compiler.

import Mathlib
import Definitions.Def_NestedSeatAlloc_IntPolicy_Model
import Definitions.Def_NestedSeatAlloc_IntPolicy_CLBI
open MeasureTheory ProbabilityTheory NestedSeatAlloc.IntPolicy

theorem NestedSeatAlloc.IntPolicy.all_prefixes_clbi_of_integer_subdiff {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (X : ℕ → Ω → ℝ) (f : ℕ → ℝ) (p : ℕ → ℕ)
    (hM : IsSeatModel P X f)
    (hint : ∀ i ω, ∃ n : ℕ, X i ω = n)
    (hpos : ∀ i, 1 ≤ i → 0 < f i)
    (h20 : SubdiffCondition P X f (fun i => (p i : ℝ))) :
    ∀ k, 1 ≤ k →
      IsCLBI (expRevenue P X f (fun i => (p i : ℝ)) k) := by sorry
