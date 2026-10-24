-- Prove2me | Theorems.Thm_OAI_PiExponent_FormalInterpolation_support_finset_prod_exponents
-- name    : OAI.PiExponent.FormalInterpolation.support_finset_prod_exponents
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-24T05:14:20.473981+00:00
-- url     : https://prove2.me/theorems/2fdb3845-97ec-47f4-825d-8c71bd9e8d00
-- title:
--   Supported exponents of a finite subproduct decompose across factors
-- statement:
--   For any finite product of multivariate polynomials, each exponent in its support can be expressed as a sum of exponents supported by the factors, with one choice for each factor in the finite set.
-- source:
--   openai/math Ampleness stack: WeightedIdealCurveBound implies eps-ample exceptional twist, hence Serre vanishing and eventual generation of I^n by weight ≤ n(rho+eps) sections.

import Mathlib.Data.Complex.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous
open scoped BigOperators

theorem OAI.PiExponent.FormalInterpolation.support_finset_prod_exponents
    {ι σ : Type*} [DecidableEq σ] (s : Finset ι)
    (v : ι → MvPolynomial σ Complex) (a : σ →₀ Nat)
    (ha : a ∈ (∏ i ∈ s, v i).support) :
    ∃ b : ι → (σ →₀ Nat),
      (∀ i, i ∈ s → b i ∈ (v i).support) ∧ (∑ i ∈ s, b i) = a := by
  sorry
