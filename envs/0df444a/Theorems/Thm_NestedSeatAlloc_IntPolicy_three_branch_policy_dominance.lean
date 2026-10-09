-- Prove2me | Theorems.Thm_NestedSeatAlloc_IntPolicy_three_branch_policy_dominance
-- name    : NestedSeatAlloc.IntPolicy.three_branch_policy_dominance
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-08T14:37:05.372204+00:00
-- url     : https://prove2.me/theorems/a6530169-4a1a-4fdb-8af6-b05c75d81d34
-- title:
--   Domination of full three-branch nested revenue under a globally optimal continuation value
-- statement:
--   # Pointwise dominance of the nested three-branch revenue formula
--
--   For nonnegative realised next-class demand y, nonnegative capacity s,
--   and two nonnegative protection thresholds a (proposed) and b (rival),
--   compare the full three-branch revenue recursion, given continuation
--   functions gp for the proposed policy and gq for the rival policy.
--
--   Assume gq(t)<=gp(t) at all nonnegative capacities and gp(t)-c*t
--   is nondecreasing for t<=a and nonincreasing for t>=a. The Proved
--   three_branch_eq_clamped_allocation converts each piecewise formula
--   to an allocation clamp. The Proved clamped_surplus_dominance then
--   gives the desired inequality in a single step.
--
--   This theorem isolates the purely deterministic comparison needed
--   for a next-level condRevenue dominance theorem. No stochastic
--   integrability or concavity appears directly in the statement:
--   the monotonicity conditions are what the Proved
--   endpoint_secants_of_inSubdiff and normalized_mono_of_endpoint_secants
--   supply under CLBI-concavity and the subdifferential condition.
-- source:
--   # Pointwise dominance of the nested three-branch revenue formula
--
--   For nonnegative realised next-class demand y, nonnegative capacity s,
--   and two nonnegative protection thresholds a (proposed) and b (rival),
--   compare the full three-branch revenue recursion, given continuation
--   functions gp for the proposed policy and gq for the rival policy.
--
--   Assume gq(t)<=gp(t) at all nonnegative capacities and gp(t)-c*t
--   is nondecreasing for t<=a and nonincreasing for t>=a. The Proved
--   three_branch_eq_clamped_allocation converts each piecewise formula
--   to an allocation clamp. The Proved clamped_surplus_dominance then
--   gives the desired inequality in a single step.
--
--   This theorem isolates the purely deterministic comparison needed
--   for a next-level condRevenue dominance theorem. No stochastic
--   integrability or concavity appears directly in the statement:
--   the monotonicity conditions are what the Proved
--   endpoint_secants_of_inSubdiff and normalized_mono_of_endpoint_secants
--   supply under CLBI-concavity and the subdifferential condition.

import Mathlib
import Definitions.Def_NestedSeatAlloc_IntPolicy_Model
open MeasureTheory ProbabilityTheory NestedSeatAlloc.IntPolicy

theorem NestedSeatAlloc.IntPolicy.three_branch_policy_dominance (gq gp : ℝ → ℝ) (c a b y s : ℝ)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hy : 0 ≤ y) (hs : 0 ≤ s)
    (hdom : ∀ t, 0 ≤ t → gq t ≤ gp t)
    (hleft : ∀ u v, 0 ≤ u → u ≤ v → v ≤ a →
      gp u - c * u ≤ gp v - c * v)
    (hright : ∀ u v, a ≤ u → u ≤ v →
      gp v - c * v ≤ gp u - c * u) :
    (if s < b then gq s else if s < b + y then
      (s - b) * c + gq b else y * c + gq (s - y)) ≤
    (if s < a then gp s else if s < a + y then
      (s - a) * c + gp a else y * c + gp (s - y)) := by sorry
