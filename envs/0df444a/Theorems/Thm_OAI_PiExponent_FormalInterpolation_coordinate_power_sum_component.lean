-- Prove2me | Theorems.Thm_OAI_PiExponent_FormalInterpolation_coordinate_power_sum_component
-- name    : OAI.PiExponent.FormalInterpolation.coordinate_power_sum_component
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-23T11:56:10.831013+00:00
-- url     : https://prove2.me/theorems/6e2dc1ba-1073-40bc-b246-96b7d4ed35ca
-- title:
--   A coordinate-power sum has distinct weighted components
-- statement:
--   Projecting a finite sum of scalar multiples of powers of coordinate i to weighted degree n · w(i) returns its n-th term. Positivity of w(i) makes the degrees of distinct natural exponents different, including exponent zero.
-- source:
--   openai/math Ampleness stack: WeightedIdealCurveBound implies eps-ample exceptional twist, hence Serre vanishing and eventual generation of I^n by weight ≤ n(rho+eps) sections.

import Mathlib.Data.Complex.Basic
import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous

open scoped BigOperators

theorem OAI.PiExponent.FormalInterpolation.coordinate_power_sum_component
    {d : Nat} (w : Fin d → ℚ)
    (hw : ∀ i, 0 < (w i : ℝ))
    (i : Fin d) (K : Nat) (c : Fin (K + 1) → ℂ)
    (n : Fin (K + 1)) :
    MvPolynomial.weightedHomogeneousComponent w
      (((n : ℕ) : ℚ) * w i)
      (∑ k : Fin (K + 1), MvPolynomial.C (c k) *
        (MvPolynomial.X i : MvPolynomial (Fin d) ℂ) ^ (k : Nat)) =
      MvPolynomial.C (c n) * (MvPolynomial.X i : MvPolynomial (Fin d) ℂ) ^ (n : Nat) := by sorry
