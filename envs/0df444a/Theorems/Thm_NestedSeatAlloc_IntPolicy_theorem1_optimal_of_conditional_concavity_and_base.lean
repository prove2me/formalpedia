-- Prove2me | Theorems.Thm_NestedSeatAlloc_IntPolicy_theorem1_optimal_of_conditional_concavity_and_base
-- name    : NestedSeatAlloc.IntPolicy.theorem1_optimal_of_conditional_concavity_and_base
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-08T15:56:48.264325+00:00
-- url     : https://prove2.me/theorems/a5a07ac3-4f76-4352-951c-fae8a83a16a9
-- title:
--   Subdifferential protection policies with concave base and conditional revenues are optimal
-- statement:
--   If policy p satisfies the subdifferential condition, and base-class
--   expected revenue is concave, and all later conditional revenue
--   functions are concave for nonnegative demands, then p is optimal.
--   The proven corollary1_integrate_conditional_concavity integrates
--   conditional concavity into expected-revenue concavity for each
--   class k>=2. The base-class hypothesis supplies k=1.
--   Apply the newly proven theorem1_global_optimality_of_prefix_concavity
--   to obtain IsOptimal for all competitors and capacities.
--   This is a sound decomposition of the still-open general Theorem 1.
--   No local Lean was run; submit to remote verifier only.
-- source:
--   If policy p satisfies the subdifferential condition, and base-class
--   expected revenue is concave, and all later conditional revenue
--   functions are concave for nonnegative demands, then p is optimal.
--   The proven corollary1_integrate_conditional_concavity integrates
--   conditional concavity into expected-revenue concavity for each
--   class k>=2. The base-class hypothesis supplies k=1.
--   Apply the newly proven theorem1_global_optimality_of_prefix_concavity
--   to obtain IsOptimal for all competitors and capacities.
--   This is a sound decomposition of the still-open general Theorem 1.
--   No local Lean was run; submit to remote verifier only.

import Mathlib
import Definitions.Def_NestedSeatAlloc_IntPolicy_Model
open MeasureTheory ProbabilityTheory NestedSeatAlloc.IntPolicy

theorem NestedSeatAlloc.IntPolicy.theorem1_optimal_of_conditional_concavity_and_base {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (X : ℕ → Ω → ℝ) (f p : ℕ → ℝ)
    (hM : IsSeatModel P X f) (hp : IsProtectionPolicy p)
    (h20 : SubdiffCondition P X f p)
    (hbase : ConcaveOn ℝ (Set.Ici 0) (expRevenue P X f p 1))
    (hcond : ∀ k, 1 ≤ k → ∀ y, 0 ≤ y →
      ConcaveOn ℝ (Set.Ici 0) (condRevenue P X f p (k + 1) y)) :
    IsOptimal P X f p := by sorry
