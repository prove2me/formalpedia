-- Prove2me | Theorems.Thm_NestedSeatAlloc_IntPolicy_indep_prefix_next_demand
-- name    : NestedSeatAlloc.IntPolicy.indep_prefix_next_demand
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-08T14:12:13.572856+00:00
-- url     : https://prove2.me/theorems/c5e5a2fa-5fc2-42e5-932c-656c6a0ba8d8
-- title:
--   The next class demand is independent of the finite higher-fare demand vector
-- statement:
--   # Independence of the high-fare demand prefix and the next demand
--
--   Using the published helper indep_prefix_next_singleton, establish
--   independence of the higher-fare demand vector over indices 1..k and
--   the singleton vector at k+1. A singleton vector is itself a measurable
--   function-valued random variable. Measurable evaluation at its unique
--   index turns it into the real-valued variable X(k+1). Apply the pinned
--   Mathlib theorem ProbabilityTheory.IndepFun.comp, with the identity map
--   on the prefix vector and the measurable evaluation map on the singleton.
--   The result is IndepFun prefix (X(k+1)) P.
--
--   The exact IndepFun.comp signature was checked by the remote signature
--   probe with publication job 514ba494-2af1-4470-bb0c-b74270efba5c:
--   IndepFun f g μ -> Measurable φ -> Measurable ψ ->
--   IndepFun (φ ∘ f) (ψ ∘ g) μ.
--   The exact measurable_pi_apply declaration was checked in the pinned
--   revision source.
--
--   A successful proof allows
--   indepFun_iff_map_prod_eq_prod_map_map (with variables swapped, or using
--   IndepFun.symm) to factor the joint pushforward into a product measure.
--   This is the stochastic bridge needed for the formal identity
--   expRevenue_eq_integral_condRevenue.
--
--   Do not use this as an admitted import unless the remote compiler
--   returns ACCEPTED.
-- source:
--   # Independence of the high-fare demand prefix and the next demand
--
--   Using the published helper indep_prefix_next_singleton, establish
--   independence of the higher-fare demand vector over indices 1..k and
--   the singleton vector at k+1. A singleton vector is itself a measurable
--   function-valued random variable. Measurable evaluation at its unique
--   index turns it into the real-valued variable X(k+1). Apply the pinned
--   Mathlib theorem ProbabilityTheory.IndepFun.comp, with the identity map
--   on the prefix vector and the measurable evaluation map on the singleton.
--   The result is IndepFun prefix (X(k+1)) P.
--
--   The exact IndepFun.comp signature was checked by the remote signature
--   probe with publication job 514ba494-2af1-4470-bb0c-b74270efba5c:
--   IndepFun f g μ -> Measurable φ -> Measurable ψ ->
--   IndepFun (φ ∘ f) (ψ ∘ g) μ.
--   The exact measurable_pi_apply declaration was checked in the pinned
--   revision source.
--
--   A successful proof allows
--   indepFun_iff_map_prod_eq_prod_map_map (with variables swapped, or using
--   IndepFun.symm) to factor the joint pushforward into a product measure.
--   This is the stochastic bridge needed for the formal identity
--   expRevenue_eq_integral_condRevenue.
--
--   Do not use this as an admitted import unless the remote compiler
--   returns ACCEPTED.

import Mathlib
import Definitions.Def_NestedSeatAlloc_IntPolicy_Model
open MeasureTheory ProbabilityTheory NestedSeatAlloc.IntPolicy

theorem NestedSeatAlloc.IntPolicy.indep_prefix_next_demand
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (X : ℕ → Ω → ℝ) (f : ℕ → ℝ)
    (hM : IsSeatModel P X f) (k : ℕ) :
    IndepFun
      (fun ω : Ω => fun i : (Finset.Icc 1 k) => X i.1 ω)
      (X (k + 1)) P := by sorry
