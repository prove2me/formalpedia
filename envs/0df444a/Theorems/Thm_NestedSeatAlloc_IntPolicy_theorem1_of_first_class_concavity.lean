-- Prove2me | Theorems.Thm_NestedSeatAlloc_IntPolicy_theorem1_of_first_class_concavity
-- name    : NestedSeatAlloc.IntPolicy.theorem1_of_first_class_concavity
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-08T16:31:52.584331+00:00
-- url     : https://prove2.me/theorems/cbfe41eb-40c7-4a45-a98e-cc06b0abb064
-- title:
--   Full Theorem 1 conclusion from the first-class expected-revenue concavity and condition (20)
-- statement:
--   Correct Theorem 1 reduction with only one additional premise:
--   the expected revenue of the highest-fare class is concave on all
--   nonnegative capacities.
--
--   Induct on nest size. The previously Proved
--   corollary1_conditional_revenue_concave gives concavity of
--   the next conditional revenue using current expected-revenue
--   concavity and the subdifferential condition (20).
--   The previously Proved
--   corollary1_integrate_conditional_concavity then gives concavity
--   of the next expected revenue. This establishes all-prefix
--   expected-revenue concavity from only the first-class premise.
--
--   One final application of the Proved
--   corollary1_conditional_revenue_concave gives the first component
--   of the published Theorem 1 conclusion for all k and y.
--   The Proved theorem1_global_optimality_of_prefix_concavity
--   gives the IsOptimal second component.
--
--   This is strictly stronger than the earlier helper that assumes
--   conditional concavity at all prefixes. It explicitly avoids both
--   previously Disproved conditional base/step statements.
--   The missing mathematical obligation for the exact published
--   Theorem 1 is proving the highest-fare expected-revenue concavity
--   from the original assumptions hM, hp, h20, without silently
--   assuming nonnegative fares. No local Lean compilation.
-- source:
--   Correct Theorem 1 reduction with only one additional premise:
--   the expected revenue of the highest-fare class is concave on all
--   nonnegative capacities.
--
--   Induct on nest size. The previously Proved
--   corollary1_conditional_revenue_concave gives concavity of
--   the next conditional revenue using current expected-revenue
--   concavity and the subdifferential condition (20).
--   The previously Proved
--   corollary1_integrate_conditional_concavity then gives concavity
--   of the next expected revenue. This establishes all-prefix
--   expected-revenue concavity from only the first-class premise.
--
--   One final application of the Proved
--   corollary1_conditional_revenue_concave gives the first component
--   of the published Theorem 1 conclusion for all k and y.
--   The Proved theorem1_global_optimality_of_prefix_concavity
--   gives the IsOptimal second component.
--
--   This is strictly stronger than the earlier helper that assumes
--   conditional concavity at all prefixes. It explicitly avoids both
--   previously Disproved conditional base/step statements.
--   The missing mathematical obligation for the exact published
--   Theorem 1 is proving the highest-fare expected-revenue concavity
--   from the original assumptions hM, hp, h20, without silently
--   assuming nonnegative fares. No local Lean compilation.

import Mathlib
import Definitions.Def_NestedSeatAlloc_IntPolicy_Model
open MeasureTheory ProbabilityTheory NestedSeatAlloc.IntPolicy

theorem NestedSeatAlloc.IntPolicy.theorem1_of_first_class_concavity {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (X : ℕ → Ω → ℝ) (f p : ℕ → ℝ)
    (hM : IsSeatModel P X f) (hp : IsProtectionPolicy p)
    (h20 : SubdiffCondition P X f p)
    (hbase : ConcaveOn ℝ (Set.Ici 0) (expRevenue P X f p 1)) :
    (∀ k, 1 ≤ k → ∀ y, 0 ≤ y →
      ConcaveOn ℝ (Set.Ici 0) (condRevenue P X f p (k + 1) y)) ∧
      IsOptimal P X f p := by sorry
