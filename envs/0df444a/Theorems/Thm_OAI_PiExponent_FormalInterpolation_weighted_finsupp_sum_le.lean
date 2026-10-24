-- Prove2me | Theorems.Thm_OAI_PiExponent_FormalInterpolation_weighted_finsupp_sum_le
-- name    : OAI.PiExponent.FormalInterpolation.weighted_finsupp_sum_le
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-23T12:03:13.670077+00:00
-- url     : https://prove2.me/theorems/7bea054d-e7cb-4065-a877-fe10fd9c5c3e
-- title:
--   Weight bound for a finite sum of supported exponents
-- statement:
--   If each selected exponent is supported in its corresponding polynomial and satisfies the stated per-factor weight bound, then the weight of their finite sum is at most the sum of the bounds. Prove by linearity of Finsupp evaluation and exchanging finite sums; the empty index type gives zero on both sides.
-- source:
--   openai/math Ampleness stack: WeightedIdealCurveBound implies eps-ample exceptional twist, hence Serre vanishing and eventual generation of I^n by weight ≤ n(rho+eps) sections.

import Mathlib.Data.Real.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous

open scoped BigOperators

theorem OAI.PiExponent.FormalInterpolation.weighted_finsupp_sum_le
    {σ ι : Type*} [Fintype σ] [Fintype ι]
    (w : σ → Rat) (f : ι → MvPolynomial σ Complex) (B : ι → Real)
    (b : ι → σ →₀ Nat) (hb : ∀ i, b i ∈ (f i).support)
    (hbound : ∀ i, ∀ c ∈ (f i).support,
      ∑ k, (w k : Real) * (c k : Real) ≤ B i) :
    ∑ k, (w k : Real) * ((∑ i, b i) k : Real) ≤ ∑ i, B i := by sorry
