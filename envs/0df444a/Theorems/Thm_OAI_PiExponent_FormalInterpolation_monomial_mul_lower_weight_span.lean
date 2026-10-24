-- Prove2me | Theorems.Thm_OAI_PiExponent_FormalInterpolation_monomial_mul_lower_weight_span
-- name    : OAI.PiExponent.FormalInterpolation.monomial_mul_lower_weight_span
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-23T13:34:11.398987+00:00
-- url     : https://prove2.me/theorems/f2a72970-c4d7-401a-9618-405263d63bf0
-- title:
--   Monomial multiplication preserves strict lower weight
-- statement:
--   Multiplying a polynomial in the A-span of monomials of weight strictly below L by the monomial with exponent c puts it in the A-span of monomials of weight strictly below the weight of c plus L. The strict inequality remains strict, including when the added weight is zero.
-- source:
--   openai/math Ampleness stack: WeightedIdealCurveBound implies eps-ample exceptional twist, hence Serre vanishing and eventual generation of I^n by weight ≤ n(rho+eps) sections.

import Mathlib.Data.Real.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous

open scoped BigOperators

theorem OAI.PiExponent.FormalInterpolation.monomial_mul_lower_weight_span {d : Nat} (A : Subalgebra ℂ (MvPolynomial (Fin d) ℂ)) (W : Fin d → Nat) (c : Fin d →₀ Nat) (L : Nat) (p : MvPolynomial (Fin d) ℂ) (hp : p ∈ Submodule.span A {f : MvPolynomial (Fin d) ℂ | ∃ a : Fin d →₀ Nat, (∑ k : Fin d, a k * W k) < L ∧ f = MvPolynomial.monomial a (1 : ℂ)}) : MvPolynomial.monomial c (1 : ℂ) * p ∈ Submodule.span A {f : MvPolynomial (Fin d) ℂ | ∃ b : Fin d →₀ Nat, (∑ k : Fin d, b k * W k) < (∑ k : Fin d, c k * W k) + L ∧ f = MvPolynomial.monomial b (1 : ℂ)} := by sorry
