-- Prove2me | Theorems.Thm_NestedSeatAlloc_IntPolicy_expRevenue_eq_integral_condRevenue
-- name    : NestedSeatAlloc.IntPolicy.expRevenue_eq_integral_condRevenue
-- status  : Open
-- author  : @WillR
-- created : 2026-10-08T12:52:45.290995+00:00
-- url     : https://prove2.me/theorems/a5666e8a-fe70-4ded-920b-585f3a37445a
-- title:
--   Expected next-class revenue is the marginal integral of conditional revenue under independent demands
-- statement:
--   # Independence-based integration of conditional next-class revenue
--
--   This is the missing stochastic identity for Theorem 1's all-seats optimality
--   step. The paper's model assumes the demands X_1,X_2,... are mutually
--   independent and measurable, nonnegative random variables. The nested revenue
--   R_(k+1) depends on the first k demands and on X_(k+1). The definition
--   condRevenue P X f p (k+1) y s freezes X_(k+1) to y while taking expected
--   revenue over the remaining random coordinates.
--
--   By independence, the law of (X_1,...,X_k,X_(k+1)) factors as the product of
--   the first-k joint law and the marginal distribution of X_(k+1). Integrating
--   first over the first-k law at fixed y produces condRevenue(...,y,s).
--   Integrating that result with respect to the law of X_(k+1) recovers the
--   unconditional expected revenue.
--
--   The formal proof should:
--   (1) build the measurable prefix vector U : Ω -> Finset.Icc 1 k -> ℝ;
--   (2) establish that U and X_(k+1) are independent using hM.indep;
--   (3) use the pushforward/product law identity and Fubini/Tonelli for the
--   integrable revenue, with integrability from the already Proved
--   revenue_integrable_of_seat_model;
--   (4) use the already Proved condRevenue_eq_integral_prefix_law to identify
--   the inner integral with the defined condRevenue;
--   (5) apply integral_map for the marginal demand distribution.
--
--   No extra finiteness or moment assumption is required for s>=0 because
--   the existing model and integrability lemma bound realised revenue for
--   fixed s and finite k.
--
--   This theorem is explicitly an OPEN proof obligation at publication.
--   It cannot be assumed proved or used to promote a sketch to a proof.
--   Together with conditional_optimality_with_concavity it gives the
--   required lift from a pointwise conditional inequality to unconditional
--   expected-revenue dominance.
--
--   Pinned environment: 0df444a360eaa60ab8c11dca51a86af692955474.
-- source:
--   # Independence-based integration of conditional next-class revenue
--
--   This is the missing stochastic identity for Theorem 1's all-seats optimality
--   step. The paper's model assumes the demands X_1,X_2,... are mutually
--   independent and measurable, nonnegative random variables. The nested revenue
--   R_(k+1) depends on the first k demands and on X_(k+1). The definition
--   condRevenue P X f p (k+1) y s freezes X_(k+1) to y while taking expected
--   revenue over the remaining random coordinates.
--
--   By independence, the law of (X_1,...,X_k,X_(k+1)) factors as the product of
--   the first-k joint law and the marginal distribution of X_(k+1). Integrating
--   first over the first-k law at fixed y produces condRevenue(...,y,s).
--   Integrating that result with respect to the law of X_(k+1) recovers the
--   unconditional expected revenue.
--
--   The formal proof should:
--   (1) build the measurable prefix vector U : Ω -> Finset.Icc 1 k -> ℝ;
--   (2) establish that U and X_(k+1) are independent using hM.indep;
--   (3) use the pushforward/product law identity and Fubini/Tonelli for the
--   integrable revenue, with integrability from the already Proved
--   revenue_integrable_of_seat_model;
--   (4) use the already Proved condRevenue_eq_integral_prefix_law to identify
--   the inner integral with the defined condRevenue;
--   (5) apply integral_map for the marginal demand distribution.
--
--   No extra finiteness or moment assumption is required for s>=0 because
--   the existing model and integrability lemma bound realised revenue for
--   fixed s and finite k.
--
--   This theorem is explicitly an OPEN proof obligation at publication.
--   It cannot be assumed proved or used to promote a sketch to a proof.
--   Together with conditional_optimality_with_concavity it gives the
--   required lift from a pointwise conditional inequality to unconditional
--   expected-revenue dominance.
--
--   Pinned environment: 0df444a360eaa60ab8c11dca51a86af692955474.

import Mathlib
import Definitions.Def_NestedSeatAlloc_IntPolicy_Model
open MeasureTheory ProbabilityTheory NestedSeatAlloc.IntPolicy

theorem NestedSeatAlloc.IntPolicy.expRevenue_eq_integral_condRevenue
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (X : ℕ → Ω → ℝ) (f p : ℕ → ℝ)
    (hM : IsSeatModel P X f) (hp : IsProtectionPolicy p)
    (k : ℕ) (hk : 1 ≤ k) (s : ℝ) (hs : 0 ≤ s) :
    expRevenue P X f p (k + 1) s =
      ∫ y : ℝ, condRevenue P X f p (k + 1) y s
        ∂(Measure.map (X (k + 1)) P) := by sorry
