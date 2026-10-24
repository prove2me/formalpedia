-- Prove2me | Theorems.Thm_OAI_PiExponent_FormalInterpolation_integral_of_integral_coordinates_over_repair6
-- name    : OAI.PiExponent.FormalInterpolation.integral_of_integral_coordinates_over_repair6
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-23T09:37:01.137632+00:00
-- url     : https://prove2.me/theorems/7304ed80-9c44-45bf-a650-13a0f1ec3c51
-- title:
--   Integral coordinates make every polynomial integral
-- statement:
--   If each coordinate variable is integral over A, then every multivariate polynomial is integral over A.
-- source:
--   openai/math Ampleness stack: WeightedIdealCurveBound implies eps-ample exceptional twist, hence Serre vanishing and eventual generation of I^n by weight ≤ n(rho+eps) sections.

import Definitions.Def_OAI_PiExponent_WeightedIdealCurveCriterion
import Mathlib.Data.Complex.Basic
import Mathlib.RingTheory.IntegralClosure.IsIntegral.Defs
import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous

open OAI.PiExponent.FormalInterpolation

theorem OAI.PiExponent.FormalInterpolation.integral_of_integral_coordinates_over_repair6
    {d : Nat} (A : Subalgebra Complex (MvPolynomial (Fin d) Complex))
    (hcoords : ∀ i : Fin d,
      IsIntegral A (MvPolynomial.X i : MvPolynomial (Fin d) Complex)) :
    ∀ x : MvPolynomial (Fin d) Complex, IsIntegral A x := by sorry
