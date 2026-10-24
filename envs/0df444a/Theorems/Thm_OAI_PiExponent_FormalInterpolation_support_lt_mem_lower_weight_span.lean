-- Prove2me | Theorems.Thm_OAI_PiExponent_FormalInterpolation_support_lt_mem_lower_weight_span
-- name    : OAI.PiExponent.FormalInterpolation.support_lt_mem_lower_weight_span
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-23T13:09:36.882709+00:00
-- url     : https://prove2.me/theorems/2747e2f5-8fcc-4fcb-98a6-d9ac98182d1a
-- title:
--   A support-wise weight bound gives span membership
-- statement:
--   If every exponent in a polynomial’s support has natural weighted degree below `B`, then the polynomial lies in the complex span of the monomials with weighted degree below `B`. Expand over the finite support and use closure of the span under finite sums and scalar multiplication.
-- source:
--   openai/math Ampleness stack: WeightedIdealCurveBound implies eps-ample exceptional twist, hence Serre vanishing and eventual generation of I^n by weight ≤ n(rho+eps) sections.

import Mathlib.Data.Real.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous

open scoped BigOperators

theorem OAI.PiExponent.FormalInterpolation.support_lt_mem_lower_weight_span {d : Nat} (W : Fin d → Nat) (B : Nat) (q : MvPolynomial (Fin d) ℂ) (hq : ∀ a : Fin d →₀ Nat, a ∈ q.support → (∑ k : Fin d, a k * W k) < B) : q ∈ Submodule.span ℂ {f : MvPolynomial (Fin d) ℂ | ∃ a : Fin d →₀ Nat, (∑ k : Fin d, a k * W k) < B ∧ f = MvPolynomial.monomial a (1 : ℂ)} := by sorry
