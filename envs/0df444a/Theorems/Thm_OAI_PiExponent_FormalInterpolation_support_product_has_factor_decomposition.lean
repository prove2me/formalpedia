-- Prove2me | Theorems.Thm_OAI_PiExponent_FormalInterpolation_support_product_has_factor_decomposition
-- name    : OAI.PiExponent.FormalInterpolation.support_product_has_factor_decomposition
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-23T12:02:52.425857+00:00
-- url     : https://prove2.me/theorems/f7e4f74f-fa58-467e-93a4-c4afd6bbd63c
-- title:
--   Support exponents of a finite product decompose factorwise
-- statement:
--   Every exponent in the support of a finite product of multivariate polynomials is a sum of exponents, one chosen from the support of each factor. The empty product case requires the empty sum to be zero.
-- source:
--   openai/math Ampleness stack: WeightedIdealCurveBound implies eps-ample exceptional twist, hence Serre vanishing and eventual generation of I^n by weight ≤ n(rho+eps) sections.

import Mathlib.Data.Real.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous

open scoped BigOperators

theorem OAI.PiExponent.FormalInterpolation.support_product_has_factor_decomposition
    {σ ι : Type*} [Fintype σ] [Fintype ι]
    (f : ι → MvPolynomial σ Complex) (a : σ →₀ Nat)
    (ha : a ∈ (∏ i, f i).support) :
    ∃ b : ι → σ →₀ Nat, (∀ i, b i ∈ (f i).support) ∧ a = ∑ i, b i := by sorry
