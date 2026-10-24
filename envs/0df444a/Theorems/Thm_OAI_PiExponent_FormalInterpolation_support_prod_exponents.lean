-- Prove2me | Theorems.Thm_OAI_PiExponent_FormalInterpolation_support_prod_exponents
-- name    : OAI.PiExponent.FormalInterpolation.support_prod_exponents
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-24T05:01:14.908006+00:00
-- url     : https://prove2.me/theorems/2f83cdd7-277e-488c-8489-a92eee4f7e38
-- title:
--   Supported exponents of a finite product decompose across factors
-- statement:
--   Every exponent in the support of a finite product is a sum of one supported exponent from each factor. For the empty product, the sum is zero. The proof route is induction on the finite index type using the support-of-product inclusion from `MvPolynomial.support_mul`.
-- source:
--   openai/math Ampleness stack: WeightedIdealCurveBound implies eps-ample exceptional twist, hence Serre vanishing and eventual generation of I^n by weight ≤ n(rho+eps) sections.

import Mathlib.Data.Complex.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous
open scoped BigOperators

theorem OAI.PiExponent.FormalInterpolation.support_prod_exponents {d m : Nat} (v : Fin m → MvPolynomial (Fin d) Complex) (a : Fin d →₀ Nat) (ha : a ∈ (∏ i, v i).support) : ∃ b : Fin m → (Fin d →₀ Nat), (∀ i, b i ∈ (v i).support) ∧ (∑ i, b i) = a := by sorry
