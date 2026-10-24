-- Prove2me | Theorems.Thm_OAI_PiExponent_FormalInterpolation_monomials_span_of_lower_weight_bounds
-- name    : OAI.PiExponent.FormalInterpolation.monomials_span_of_lower_weight_bounds
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-23T12:54:55.199527+00:00
-- url     : https://prove2.me/theorems/06d8a09c-16f1-4bae-82f3-8aea57ebf9f8
-- title:
--   Matching lower-weight power relations span every monomial from a bounded rectangle
-- statement:
--   If each coordinate power with exponent n i is in the subalgebra-span of monomials of strictly smaller weighted degree, then every monomial is in the span of monomials whose exponents are all below those same bounds.
-- source:
--   openai/math Ampleness stack: WeightedIdealCurveBound implies eps-ample exceptional twist, hence Serre vanishing and eventual generation of I^n by weight ≤ n(rho+eps) sections.

import Mathlib.Data.Real.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous

open scoped BigOperators

theorem OAI.PiExponent.FormalInterpolation.monomials_span_of_lower_weight_bounds {d : Nat} (A : Subalgebra ℂ (MvPolynomial (Fin d) ℂ)) (W : Fin d → Nat) (hW : ∀ i, 0 < W i) (n : Fin d → Nat) (hn : ∀ i, 0 < n i) (hred : ∀ i : Fin d, (MvPolynomial.X i : MvPolynomial (Fin d) ℂ) ^ n i ∈ Submodule.span A {f : MvPolynomial (Fin d) ℂ | ∃ a : Fin d →₀ Nat, (∑ k : Fin d, a k * W k) < n i * W i ∧ f = MvPolynomial.monomial a (1 : ℂ)}) : ∀ e : Fin d →₀ Nat, MvPolynomial.monomial e (1 : ℂ) ∈ Submodule.span A {f : MvPolynomial (Fin d) ℂ | ∃ a : Fin d →₀ Nat, (∀ i, a i < n i) ∧ f = MvPolynomial.monomial a (1 : ℂ)} := by sorry
