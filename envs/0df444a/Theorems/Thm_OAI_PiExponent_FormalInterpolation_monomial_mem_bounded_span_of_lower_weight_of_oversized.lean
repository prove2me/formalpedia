-- Prove2me | Theorems.Thm_OAI_PiExponent_FormalInterpolation_monomial_mem_bounded_span_of_lower_weight_of_oversized
-- name    : OAI.PiExponent.FormalInterpolation.monomial_mem_bounded_span_of_lower_weight_of_oversized
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-23T13:08:28.682013+00:00
-- url     : https://prove2.me/theorems/93f90fe9-c7ee-4c96-b10e-ef94f3ada6b9
-- title:
--   Reduce an oversized monomial using lower-weight coordinate relations
-- statement:
--   If e has at least one coordinate at or above its bound, then its monomial lies in the bounded-monomial span, provided each coordinate-power relation reduces to strictly lower weight and all monomials of weight below e are already in that span.
-- source:
--   openai/math Ampleness stack: WeightedIdealCurveBound implies eps-ample exceptional twist, hence Serre vanishing and eventual generation of I^n by weight ≤ n(rho+eps) sections.

import Mathlib.Data.Real.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous

open scoped BigOperators

theorem OAI.PiExponent.FormalInterpolation.monomial_mem_bounded_span_of_lower_weight_of_oversized {d : Nat} (A : Subalgebra ℂ (MvPolynomial (Fin d) ℂ)) (W : Fin d → Nat) (hW : ∀ i, 0 < W i) (n : Fin d → Nat) (hn : ∀ i, 0 < n i) (hred : ∀ i : Fin d, (MvPolynomial.X i : MvPolynomial (Fin d) ℂ) ^ n i ∈ Submodule.span A {f : MvPolynomial (Fin d) ℂ | ∃ a : Fin d →₀ Nat, (∑ k : Fin d, a k * W k) < n i * W i ∧ f = MvPolynomial.monomial a (1 : ℂ)}) (e : Fin d →₀ Nat) (hover : ∃ i : Fin d, n i ≤ e i) (hbelow : ∀ b : Fin d →₀ Nat, (∑ k : Fin d, b k * W k) < (∑ k : Fin d, e k * W k) → MvPolynomial.monomial b (1 : ℂ) ∈ Submodule.span A {f : MvPolynomial (Fin d) ℂ | ∃ a : Fin d →₀ Nat, (∀ i, a i < n i) ∧ f = MvPolynomial.monomial a (1 : ℂ)}) : MvPolynomial.monomial e (1 : ℂ) ∈ Submodule.span A {f : MvPolynomial (Fin d) ℂ | ∃ a : Fin d →₀ Nat, (∀ i, a i < n i) ∧ f = MvPolynomial.monomial a (1 : ℂ)} := by sorry
