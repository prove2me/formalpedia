-- Prove2me | Theorems.Thm_OAI_PiExponent_FormalInterpolation_weighted_component_span_pow_product
-- name    : OAI.PiExponent.FormalInterpolation.weighted_component_span_pow_product
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-24T04:21:47.2345+00:00
-- url     : https://prove2.me/theorems/2dd7c94e-d2b6-46b5-a7c3-4fec693dadc0
-- title:
--   Products of weighted components give a higher-degree component
-- statement:
--   For any `m` source witnesses with the stated ideal-power and support bounds, their degree-`q` components multiply to an element of the target span, witnessed by the product of the original polynomials.
-- source:
--   openai/math Ampleness stack: WeightedIdealCurveBound implies eps-ample exceptional twist, hence Serre vanishing and eventual generation of I^n by weight ≤ n(rho+eps) sections.

import Mathlib.Data.Complex.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous
open scoped BigOperators

theorem OAI.PiExponent.FormalInterpolation.weighted_component_span_pow_product {d : Nat} (I : Ideal (MvPolynomial (Fin d) Complex)) (w : Fin d → Rat) (s m : Nat) (q D : Rat) (hs : 0 < s) (hD : q * (m : Rat) = D) (u : Fin m → {g : MvPolynomial (Fin d) Complex // g ∈ I ^ s ∧ ∀ a ∈ g.support, ∑ j, (w j : Real) * (a j : Real) ≤ (q : Real)}) : (∏ i, MvPolynomial.weightedHomogeneousComponent (fun j => (w j : ℚ)) q (u i).1) ∈ Ideal.span {h : MvPolynomial (Fin d) Complex | ∃ g : MvPolynomial (Fin d) Complex, g ∈ I ^ (s * m) ∧ (∀ a ∈ g.support, ∑ k, (w k : Real) * (a k : Real) ≤ (D : Real)) ∧ h = MvPolynomial.weightedHomogeneousComponent (fun k => (w k : ℚ)) D g} := by sorry
