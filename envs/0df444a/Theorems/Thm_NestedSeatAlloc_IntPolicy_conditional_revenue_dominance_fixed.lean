-- Prove2me | Theorems.Thm_NestedSeatAlloc_IntPolicy_conditional_revenue_dominance_fixed
-- name    : NestedSeatAlloc.IntPolicy.conditional_revenue_dominance_fixed
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-08T14:34:26.282469+00:00
-- url     : https://prove2.me/theorems/5008942b-2a16-4a37-9ef7-addc5401cc12
-- title:
--   Conditional next-class revenue dominance for a fixed rival under concavity and the subdifferential condition
-- statement:
--   # Conditional one-step dominance for fixed rival, seat count and demand
--
--   The previous proposed conditional_optimality_with_concavity theorem
--   timed out during server publication compilation. This reduced form fixes
--   the rival policy q, prefix depth k, seat count s and realised demand y
--   instead of quantifying over all q,y inside the theorem's conclusion.
--
--   Assume through class k the proposed policy's expected revenue dominates
--   the fixed rival at all nonnegative capacities. Assume the proposed
--   continuation expected revenue is concave on [0,infinity) and its
--   subdifferential at protection p(k) contains the next fare f(k+1).
--
--   By the Proved revenue_integrable_of_seat_model and
--   condRevenue_three_branch, both policies have the exact three-branch
--   conditional revenue formula. The Proved endpoint_secants_of_inSubdiff
--   and normalized_mono_of_endpoint_secants yield monotonicity of
--   ER_k(p,t)-f(k+1)*t to the left and right of protection p(k).
--   The published three_branch_policy_dominance lemma then compares
--   the complete conditional recursions.
--
--   For the direct integer policy from theorem2_integer_subdiff_policy_exists,
--   the Proved all_prefixes_clbi_of_integer_subdiff supplies the concavity
--   premise at every depth. The conditional result can be integrated using
--   expRevenue_eq_integral_condRevenue once the stochastic identity is proved.
--
--   All candidate files are source-only until the remote Prove2Me compiler
--   returns an ACCEPTED proof.
-- source:
--   # Conditional one-step dominance for fixed rival, seat count and demand
--
--   The previous proposed conditional_optimality_with_concavity theorem
--   timed out during server publication compilation. This reduced form fixes
--   the rival policy q, prefix depth k, seat count s and realised demand y
--   instead of quantifying over all q,y inside the theorem's conclusion.
--
--   Assume through class k the proposed policy's expected revenue dominates
--   the fixed rival at all nonnegative capacities. Assume the proposed
--   continuation expected revenue is concave on [0,infinity) and its
--   subdifferential at protection p(k) contains the next fare f(k+1).
--
--   By the Proved revenue_integrable_of_seat_model and
--   condRevenue_three_branch, both policies have the exact three-branch
--   conditional revenue formula. The Proved endpoint_secants_of_inSubdiff
--   and normalized_mono_of_endpoint_secants yield monotonicity of
--   ER_k(p,t)-f(k+1)*t to the left and right of protection p(k).
--   The published three_branch_policy_dominance lemma then compares
--   the complete conditional recursions.
--
--   For the direct integer policy from theorem2_integer_subdiff_policy_exists,
--   the Proved all_prefixes_clbi_of_integer_subdiff supplies the concavity
--   premise at every depth. The conditional result can be integrated using
--   expRevenue_eq_integral_condRevenue once the stochastic identity is proved.
--
--   All candidate files are source-only until the remote Prove2Me compiler
--   returns an ACCEPTED proof.

import Mathlib
import Definitions.Def_NestedSeatAlloc_IntPolicy_Model
open MeasureTheory ProbabilityTheory NestedSeatAlloc.IntPolicy

theorem NestedSeatAlloc.IntPolicy.conditional_revenue_dominance_fixed {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (X : ℕ → Ω → ℝ) (f p q : ℕ → ℝ) (k : ℕ) (s y : ℝ)
    (hM : IsSeatModel P X f) (hp : IsProtectionPolicy p)
    (hq : IsProtectionPolicy q) (hk : 1 ≤ k)
    (hs : 0 ≤ s) (hy : 0 ≤ y)
    (hdom : ∀ t, 0 ≤ t →
      expRevenue P X f q k t ≤ expRevenue P X f p k t)
    (hconc : ConcaveOn ℝ (Set.Ici 0) (expRevenue P X f p k))
    (hsub : InSubdiff (expRevenue P X f p k) (p k) (f (k + 1))) :
    condRevenue P X f q (k + 1) y s ≤
      condRevenue P X f p (k + 1) y s := by sorry
