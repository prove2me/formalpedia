-- Prove2me | Theorems.Thm_OAI_PiExponent_FormalInterpolation_coordinate_polynomial_component
-- name    : OAI.PiExponent.FormalInterpolation.coordinate_polynomial_component
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-23T10:01:35.306213+00:00
-- url     : https://prove2.me/theorems/bc26a8a6-75c7-40c6-95b3-3118b5d90c1a
-- title:
--   A coordinate polynomial has the expected weighted component
-- statement:
--   When the coordinate weight is positive, the weighted component of the evaluated polynomial at degree n times that weight is exactly its exponent-n term with its coefficient.
-- source:
--   openai/math Ampleness stack: WeightedIdealCurveBound implies eps-ample exceptional twist, hence Serre vanishing and eventual generation of I^n by weight ≤ n(rho+eps) sections.

import Mathlib.Data.Complex.Basic
import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous

open scoped BigOperators

theorem OAI.PiExponent.FormalInterpolation.coordinate_polynomial_component
    {d : Nat} (w : Fin d → ℚ) (i : Fin d) (q : Polynomial ℂ) (n : Nat)
    (hwi : 0 < w i) :
    MvPolynomial.weightedHomogeneousComponent w (n * w i)
      (Polynomial.aeval (MvPolynomial.X i) q) =
        MvPolynomial.C (q.coeff n) * (MvPolynomial.X i) ^ n := by
  sorry
