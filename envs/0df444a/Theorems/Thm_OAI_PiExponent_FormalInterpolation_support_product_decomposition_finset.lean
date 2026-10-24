-- Prove2me | Theorems.Thm_OAI_PiExponent_FormalInterpolation_support_product_decomposition_finset
-- name    : OAI.PiExponent.FormalInterpolation.support_product_decomposition_finset
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-23T12:11:26.792351+00:00
-- url     : https://prove2.me/theorems/23ebd7a7-1d81-4b43-b11e-74fa7f992a04
-- title:
--   Factorwise decomposition for a finite subproduct
-- statement:
--   For any finite set of indices, every exponent in the support of the corresponding polynomial subproduct is a sum of one supported exponent from each factor indexed by that set.
-- source:
--   openai/math Ampleness stack: WeightedIdealCurveBound implies eps-ample exceptional twist, hence Serre vanishing and eventual generation of I^n by weight ≤ n(rho+eps) sections.

import Mathlib.Data.Real.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous

open scoped BigOperators

theorem OAI.PiExponent.FormalInterpolation.support_product_decomposition_finset
    {σ ι : Type*} [DecidableEq σ]
    (s : Finset ι) (f : ι → MvPolynomial σ Complex) (a : σ →₀ Nat)
    (ha : a ∈ (∏ i ∈ s, f i).support) :
    ∃ b : ι → σ →₀ Nat,
      (∀ i, i ∈ s → b i ∈ (f i).support) ∧ a = ∑ i ∈ s, b i := by sorry
