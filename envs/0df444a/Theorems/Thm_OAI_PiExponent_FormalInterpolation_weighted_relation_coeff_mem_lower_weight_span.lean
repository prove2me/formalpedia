-- Prove2me | Theorems.Thm_OAI_PiExponent_FormalInterpolation_weighted_relation_coeff_mem_lower_weight_span
-- name    : OAI.PiExponent.FormalInterpolation.weighted_relation_coeff_mem_lower_weight_span
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-23T13:05:24.371581+00:00
-- url     : https://prove2.me/theorems/2410b284-ec16-4859-a0ff-64ea89ed26c3
-- title:
--   A supported coefficient lies in the lower-weight monomial span
-- statement:
--   If every exponent in a polynomial’s support has integer weighted degree `n * W i - delta`, with `delta > 0`, then the polynomial lies in the complex span of monomials whose natural weighted degree is strictly below `n * W i`. This follows by converting the integer degree equality to the natural degree bound and expanding the polynomial over its finite support; when the bound would be negative, the support is empty.
-- source:
--   openai/math Ampleness stack: WeightedIdealCurveBound implies eps-ample exceptional twist, hence Serre vanishing and eventual generation of I^n by weight ≤ n(rho+eps) sections.

import Mathlib.Data.Real.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous

open scoped BigOperators

theorem OAI.PiExponent.FormalInterpolation.weighted_relation_coeff_mem_lower_weight_span {d : Nat} (W : Fin d → Nat) (delta : Nat) (hdelta : 0 < delta) (n : Nat) (i : Fin d) (q : MvPolynomial (Fin d) ℂ) (hq : ∀ a : Fin d →₀ Nat, a ∈ q.support → (∑ k : Fin d, (a k : ℤ) * (W k : ℤ)) = (n : ℤ) * (W i : ℤ) - (delta : ℤ)) : q ∈ Submodule.span ℂ {f : MvPolynomial (Fin d) ℂ | ∃ a : Fin d →₀ Nat, (∑ k : Fin d, a k * W k) < n * W i ∧ f = MvPolynomial.monomial a (1 : ℂ)} := by sorry
