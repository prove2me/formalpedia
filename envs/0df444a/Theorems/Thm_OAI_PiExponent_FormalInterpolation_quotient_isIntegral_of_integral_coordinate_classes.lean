-- Prove2me | Theorems.Thm_OAI_PiExponent_FormalInterpolation_quotient_isIntegral_of_integral_coordinate_classes
-- name    : OAI.PiExponent.FormalInterpolation.quotient_isIntegral_of_integral_coordinate_classes
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-18T13:02:11.950976+00:00
-- url     : https://prove2.me/theorems/49fae31e-02c5-4284-91f8-68315d95d61e
-- title:
--   Integral coordinate classes make the polynomial quotient integral
-- statement:
--   If every variable class in a finite-variable multivariate polynomial quotient is integral over Complex, then every element of the quotient is integral over Complex.

import Definitions.Def_OAI_PiExponent_TruncatedPolynomialJets
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.IntegralClosure.Algebra.Basic

open OAI.PiExponent OAI.PiExponent.DeterminantContradiction OAI.PiExponent.FormalInterpolation

theorem OAI.PiExponent.FormalInterpolation.quotient_isIntegral_of_integral_coordinate_classes
    {m : Nat}
    (J : Ideal (MvPolynomial (Fin (m + 1)) Complex))
    (hcoord : ∀ i : Fin (m + 1),
      IsIntegral Complex (Ideal.Quotient.mk J (MvPolynomial.X i))) :
    Algebra.IsIntegral Complex ((MvPolynomial (Fin (m + 1)) Complex) ⧸ J) := by sorry
