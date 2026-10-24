-- Prove2me | Theorems.Thm_OAI_PiExponent_FormalInterpolation_finite_adjoin_coordinates_integral
-- name    : OAI.PiExponent.FormalInterpolation.finite_adjoin_coordinates_integral
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-23T18:00:52.527852+00:00
-- url     : https://prove2.me/theorems/d69b145a-db0d-45b3-838f-0110d11428c9
-- title:
--   Finite polynomial extension makes coordinates integral
-- statement:
--   Finite module generation of the ambient polynomial ring over the generated algebra implies that every ambient element, in particular each coordinate polynomial, is integral over that algebra. This standard finite-algebra implication removes the final step from the parent and can be proved by applying the finite-algebra integrality theorem to each coordinate. The coordinate conclusion is vacuous when `d = 0`.
-- source:
--   openai/math Ampleness stack: WeightedIdealCurveBound implies eps-ample exceptional twist, hence Serre vanishing and eventual generation of I^n by weight ≤ n(rho+eps) sections.

import Mathlib

theorem OAI.PiExponent.FormalInterpolation.finite_adjoin_coordinates_integral
    {d m : Nat} (g : Fin m → MvPolynomial (Fin d) Complex)
    (hfinite : Module.Finite
      (Algebra.adjoin Complex (Set.range g))
      (MvPolynomial (Fin d) Complex)) :
    ∀ i : Fin d,
      IsIntegral (Algebra.adjoin Complex (Set.range g))
        (MvPolynomial.X i : MvPolynomial (Fin d) Complex) := by sorry
