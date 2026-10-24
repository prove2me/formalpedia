-- Prove2me | Theorems.Thm_OAI_PiExponent_FormalInterpolation_weighted_support_product_le
-- name    : OAI.PiExponent.FormalInterpolation.weighted_support_product_le
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-24T04:42:25.153727+00:00
-- url     : https://prove2.me/theorems/decfc912-2224-4a06-8b5e-b557eac4e911
-- title:
--   A product preserves the summed weighted support bound
-- statement:
--   If every exponent in each polynomial of a finite family has weighted sum at most q, then every exponent in their product has weighted sum at most q*m. This isolates the support estimate needed for the witness in the parent. Prove it from the support-of-product exponent-sum formula and additivity of the weighted sum, inducting over the finite product. It permits arbitrary rational weights and q; for m = 0, the only product exponent is zero and the bound is zero.
-- source:
--   openai/math Ampleness stack: WeightedIdealCurveBound implies eps-ample exceptional twist, hence Serre vanishing and eventual generation of I^n by weight ≤ n(rho+eps) sections.

import Mathlib.Data.Complex.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous
open scoped BigOperators

theorem OAI.PiExponent.FormalInterpolation.weighted_support_product_le {d : Nat} (w : Fin d → Rat) (q : Rat) (m : Nat) (v : Fin m → MvPolynomial (Fin d) Complex) (hv : ∀ i a, a ∈ (v i).support → ∑ k, (w k : Real) * (a k : Real) ≤ (q : Real)) :
    ∀ a ∈ (∏ i, v i).support, ∑ k, (w k : Real) * (a k : Real) ≤ ((q * (m : Rat) : Rat) : Real) := by
  sorry
