-- Prove2me | Theorems.Thm_OAI_PiExponent_FormalInterpolation_span_exact_monomials_mem_expansion
-- name    : OAI.PiExponent.FormalInterpolation.span_exact_monomials_mem_expansion
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-18T13:01:20.711559+00:00
-- url     : https://prove2.me/theorems/1318baf3-f8e2-44b1-8389-ffe6e54cf388
-- title:
--   Finite expansion from a span of exact-degree monomials
-- statement:
--   Any element of the ideal spanned by exact-degree monomials in a finite family is a finite sum of those monomials multiplied by coefficients.

import Mathlib.RingTheory.MvPolynomial.Ideal

open scoped BigOperators

theorem OAI.PiExponent.FormalInterpolation.span_exact_monomials_mem_expansion
    {σ : Type*} [Fintype σ] {R : Type*} [CommSemiring R]
    (f : σ → R) (n : Nat) (p : R)
    (hp : p ∈ Ideal.span {x : R | ∃ b : σ → Nat, (∑ i, b i) = n ∧ x = ∏ i, f i ^ (b i)}) :
    ∃ (m : Nat) (b : Fin m → σ → Nat) (q : Fin m → R),
      (∀ j, (∑ i, b j i) = n) ∧
      p = ∑ j, (∏ i, f i ^ (b j i)) * q j := by sorry
