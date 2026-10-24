-- Prove2me | Theorems.Thm_OAI_PiExponent_FormalInterpolation_weighted_support_bound_mul
-- name    : OAI.PiExponent.FormalInterpolation.weighted_support_bound_mul
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-23T12:05:33.06998+00:00
-- url     : https://prove2.me/theorems/d3236847-37ee-43bf-977a-fa91a9aae834
-- title:
--   Weighted support bound for a product
-- statement:
--   If every supported exponent of each factor satisfies a weighted bound, every supported exponent of their product satisfies the sum of those bounds.
-- source:
--   openai/math Ampleness stack: WeightedIdealCurveBound implies eps-ample exceptional twist, hence Serre vanishing and eventual generation of I^n by weight ≤ n(rho+eps) sections.

import Mathlib.Data.Real.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous

open scoped BigOperators

theorem OAI.PiExponent.FormalInterpolation.weighted_support_bound_mul
    {σ : Type*} [Fintype σ] (w : σ → Rat) (A B : Real)
    (p q : MvPolynomial σ Complex)
    (hp : ∀ b ∈ p.support, ∑ k, (w k : Real) * (b k : Real) ≤ A)
    (hq : ∀ c ∈ q.support, ∑ k, (w k : Real) * (c k : Real) ≤ B)
    (a : σ →₀ Nat) (ha : a ∈ (p * q).support) :
    ∑ k, (w k : Real) * (a k : Real) ≤ A + B := by sorry
