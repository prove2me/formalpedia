-- Prove2me | Theorems.Thm_OAI_PiExponent_FormalInterpolation_monomial_mem_lower_weight_span_of_lower_weight_step
-- name    : OAI.PiExponent.FormalInterpolation.monomial_mem_lower_weight_span_of_lower_weight_step
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-23T13:25:24.721286+00:00
-- url     : https://prove2.me/theorems/f58cc28b-2eaa-409d-9197-29433bf3e068
-- title:
--   Monomial reduction to strictly lower weight
-- statement:
--   If each coordinate power is in the span of monomials of weight strictly below its weight, then every monomial whose exponent dominates one of those coordinate powers lies in the span of monomials of strictly lower total weight.
-- source:
--   openai/math Ampleness stack: WeightedIdealCurveBound implies eps-ample exceptional twist, hence Serre vanishing and eventual generation of I^n by weight ≤ n(rho+eps) sections.

import Mathlib.Data.Real.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous

open scoped BigOperators

theorem OAI.PiExponent.FormalInterpolation.monomial_mem_lower_weight_span_of_lower_weight_step {d : Nat} (A : Subalgebra ℂ (MvPolynomial (Fin d) ℂ)) (W : Fin d → Nat) (n : Fin d → Nat) (hred : ∀ i : Fin d, (MvPolynomial.X i : MvPolynomial (Fin d) ℂ) ^ n i ∈ Submodule.span A {f : MvPolynomial (Fin d) ℂ | ∃ a : Fin d →₀ Nat, (∑ k : Fin d, a k * W k) < n i * W i ∧ f = MvPolynomial.monomial a (1 : ℂ)}) (e : Fin d →₀ Nat) (hover : ∃ i : Fin d, n i ≤ e i) : MvPolynomial.monomial e (1 : ℂ) ∈ Submodule.span A {f : MvPolynomial (Fin d) ℂ | ∃ b : Fin d →₀ Nat, (∑ k : Fin d, b k * W k) < (∑ k : Fin d, e k * W k) ∧ f = MvPolynomial.monomial b (1 : ℂ)} := by sorry
