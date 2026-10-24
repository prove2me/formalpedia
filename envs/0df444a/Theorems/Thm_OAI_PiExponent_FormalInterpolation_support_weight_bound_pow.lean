-- Prove2me | Theorems.Thm_OAI_PiExponent_FormalInterpolation_support_weight_bound_pow
-- name    : OAI.PiExponent.FormalInterpolation.support_weight_bound_pow
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-23T10:12:05.959596+00:00
-- url     : https://prove2.me/theorems/f2ae0a9c-b4b2-4523-8e3f-6f0215a89e4a
-- title:
--   Weighted support bound for a polynomial power
-- statement:
--   Every supported exponent in a polynomial power has weight at most the power exponent times the bound on the original polynomial’s supported exponents. Induct on `n`; use support multiplication to decompose an exponent from the successor power into exponents from the previous power and from `f`, then add their weight bounds. At `n = 0`, the only supported exponent is zero and the bound is zero.
-- source:
--   openai/math Ampleness stack: WeightedIdealCurveBound implies eps-ample exceptional twist, hence Serre vanishing and eventual generation of I^n by weight ≤ n(rho+eps) sections.

import Mathlib.Data.Real.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous

open scoped BigOperators

theorem OAI.PiExponent.FormalInterpolation.support_weight_bound_pow
    {σ : Type*} [Fintype σ] (w : σ → Rat) (A : Real)
    (f : MvPolynomial σ Complex)
    (hbound : ∀ b ∈ f.support, ∑ k, (w k : Real) * (b k : Real) ≤ A)
    (n : Nat) (a : σ →₀ Nat) (ha : a ∈ (f ^ n).support) :
    ∑ k, (w k : Real) * (a k : Real) ≤ (n : Real) * A := by sorry
