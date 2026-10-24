-- Prove2me | Theorems.Thm_OAI_PiExponent_FormalInterpolation_monomials_span_of_degree_drop
-- name    : OAI.PiExponent.FormalInterpolation.monomials_span_of_degree_drop
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-23T12:01:09.727723+00:00
-- url     : https://prove2.me/theorems/590c9dc5-3582-4bbc-9551-151cb3f16e05
-- title:
--   Degree-dropping relations reduce monomials to a bounded rectangle
-- statement:
--   Under the target’s hypotheses, choose a positive power for each coordinate such that every monomial belongs to the span over the adjoined algebra of monomials whose exponents are below those powers in every coordinate.
-- source:
--   openai/math Ampleness stack: WeightedIdealCurveBound implies eps-ample exceptional twist, hence Serre vanishing and eventual generation of I^n by weight ≤ n(rho+eps) sections.

import Mathlib.Data.Real.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous

open scoped BigOperators

theorem OAI.PiExponent.FormalInterpolation.monomials_span_of_degree_drop {d : Nat} (w : Fin d → ℚ) (hw : ∀ i, 0 < (w i : ℝ)) (D : Nat) (hD : 0 < D) (m : Nat) (p : Fin m → MvPolynomial (Fin d) ℂ) (hrelations : ∀ i : Fin d, ∃ n : Nat, 0 < n ∧ ∃ q : Fin m → MvPolynomial (Fin d) ℂ, (MvPolynomial.X i : MvPolynomial (Fin d) ℂ) ^ n = ∑ j, q j * p j ∧ ∀ j, MvPolynomial.IsWeightedHomogeneous w (q j) ((n : ℚ) * w i - (D : ℚ))) : ∃ n : Fin d → Nat, (∀ i, 0 < n i) ∧ ∀ e : Fin d →₀ Nat, MvPolynomial.monomial e (1 : ℂ) ∈ Submodule.span (Algebra.adjoin ℂ (Set.range p)) {f : MvPolynomial (Fin d) ℂ | ∃ a : Fin d →₀ Nat, (∀ i, a i < n i) ∧ f = MvPolynomial.monomial a (1 : ℂ)} := by sorry
