-- Prove2me | Theorems.Thm_OAI_PiExponent_FormalInterpolation_support_weight_bound_fintype_prod
-- name    : OAI.PiExponent.FormalInterpolation.support_weight_bound_fintype_prod
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-23T10:12:46.801505+00:00
-- url     : https://prove2.me/theorems/ebac4b8b-5721-4bf0-9061-5d2f9c23c36c
-- title:
--   Weighted support bound for a finite product
-- statement:
--   Every supported exponent in a finite product has weight at most the sum of the per-factor bounds. Induct over the finite index set, using support multiplication and additivity of the weight; the empty product has exponent zero and bound zero.
-- source:
--   openai/math Ampleness stack: WeightedIdealCurveBound implies eps-ample exceptional twist, hence Serre vanishing and eventual generation of I^n by weight ≤ n(rho+eps) sections.

import Mathlib.Data.Real.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous

open scoped BigOperators

theorem OAI.PiExponent.FormalInterpolation.support_weight_bound_fintype_prod
    {σ ι : Type*} [Fintype σ] [Fintype ι]
    (w : σ → Rat) (f : ι → MvPolynomial σ Complex) (B : ι → Real)
    (hbound : ∀ i, ∀ b ∈ (f i).support,
      ∑ k, (w k : Real) * (b k : Real) ≤ B i)
    (a : σ →₀ Nat) (ha : a ∈ (∏ i, f i).support) :
    ∑ k, (w k : Real) * (a k : Real) ≤ ∑ i, B i := by sorry
