-- Prove2me | Theorems.Thm_OAI_PiExponent_FormalInterpolation_coordinate_power_has_lower_weight_span
-- name    : OAI.PiExponent.FormalInterpolation.coordinate_power_has_lower_weight_span
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-23T12:51:32.048522+00:00
-- url     : https://prove2.me/theorems/68b4c967-2338-4247-95f3-5f07c6495dff
-- title:
--   Coordinate powers lie in the span of strictly lower weight monomials
-- statement:
--   Each coordinate has a positive power in the algebra-span of monomials whose natural weighted degree is strictly less than that power's weighted degree.
-- source:
--   openai/math Ampleness stack: WeightedIdealCurveBound implies eps-ample exceptional twist, hence Serre vanishing and eventual generation of I^n by weight ≤ n(rho+eps) sections.

import Mathlib.Data.Real.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous

open scoped BigOperators

theorem OAI.PiExponent.FormalInterpolation.coordinate_power_has_lower_weight_span {d : Nat} (W : Fin d → Nat) (hW : ∀ i, 0 < W i) (delta : Nat) (hdelta : 0 < delta) (m : Nat) (p : Fin m → MvPolynomial (Fin d) ℂ) (hrelations : ∀ i : Fin d, ∃ n : Nat, 0 < n ∧ ∃ q : Fin m → MvPolynomial (Fin d) ℂ, (MvPolynomial.X i : MvPolynomial (Fin d) ℂ) ^ n = ∑ j, q j * p j ∧ ∀ j, ∀ a : Fin d →₀ Nat, a ∈ (q j).support → (∑ k : Fin d, (a k : ℤ) * (W k : ℤ)) = (n : ℤ) * (W i : ℤ) - (delta : ℤ)) : ∀ i : Fin d, ∃ r : Nat, 0 < r ∧ (MvPolynomial.X i : MvPolynomial (Fin d) ℂ) ^ r ∈ Submodule.span (Algebra.adjoin ℂ (Set.range p)) {f : MvPolynomial (Fin d) ℂ | ∃ a : Fin d →₀ Nat, (∑ k : Fin d, a k * W k) < r * W i ∧ f = MvPolynomial.monomial a (1 : ℂ)} := by sorry
