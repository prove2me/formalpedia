-- Prove2me | Theorems.Thm_OAI_PiExponent_FormalInterpolation_integer_weighted_monomials_span
-- name    : OAI.PiExponent.FormalInterpolation.integer_weighted_monomials_span
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-23T12:37:19.932981+00:00
-- url     : https://prove2.me/theorems/f93d3b46-7232-40c7-91ec-4e39631cf685
-- title:
--   Integer weighted degree drops yield a bounded monomial spanning set
-- statement:
--   For positive integer weights, if every coordinate has a power relation whose polynomial multipliers have support exactly one positive degree drop below that power, then every monomial lies in the algebra-span of a finite bounded rectangle. Prove this by induction on weighted degree, expanding each monomial above a cutoff with the corresponding relation and moving its generator factor into the coefficient algebra.
-- source:
--   openai/math Ampleness stack: WeightedIdealCurveBound implies eps-ample exceptional twist, hence Serre vanishing and eventual generation of I^n by weight ≤ n(rho+eps) sections.

import Mathlib.Data.Real.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous

open scoped BigOperators

theorem OAI.PiExponent.FormalInterpolation.integer_weighted_monomials_span {d : Nat} (W : Fin d → Nat) (hW : ∀ i, 0 < W i) (delta : Nat) (hdelta : 0 < delta) (m : Nat) (p : Fin m → MvPolynomial (Fin d) ℂ) (hrelations : ∀ i : Fin d, ∃ n : Nat, 0 < n ∧ ∃ q : Fin m → MvPolynomial (Fin d) ℂ, (MvPolynomial.X i : MvPolynomial (Fin d) ℂ) ^ n = ∑ j, q j * p j ∧ ∀ j, ∀ a : Fin d →₀ Nat, a ∈ (q j).support → (∑ k : Fin d, (a k : ℤ) * (W k : ℤ)) = (n : ℤ) * (W i : ℤ) - (delta : ℤ)) : ∃ n : Fin d → Nat, (∀ i, 0 < n i) ∧ ∀ e : Fin d →₀ Nat, MvPolynomial.monomial e (1 : ℂ) ∈ Submodule.span (Algebra.adjoin ℂ (Set.range p)) {f : MvPolynomial (Fin d) ℂ | ∃ a : Fin d →₀ Nat, (∀ i, a i < n i) ∧ f = MvPolynomial.monomial a (1 : ℂ)} := by sorry
