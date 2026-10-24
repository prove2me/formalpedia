-- Prove2me | Theorems.Thm_OAI_PiExponent_FormalInterpolation_curve_bound_individual_coordinate_power
-- name    : OAI.PiExponent.FormalInterpolation.curve_bound_individual_coordinate_power
-- status  : Disproved
-- author  : @Eyal1990
-- created : 2026-10-23T19:16:04.56271+00:00
-- url     : https://prove2.me/theorems/469111e6-4001-41f0-b8b6-884a9cb5bda0
-- title:
--   Curve bound gives an individual bounded coordinate power
-- statement:
--   For each coordinate separately, a positive power of that coordinate belongs to some positive ordinary power of I, with weighted degree strictly below the slope rho + eps. This removes the need to find a common ideal-power exponent at the geometric stage. For d = 0 the conclusion is vacuous. A proof route is to apply the curve-bound positivity argument to the coordinate direction on the blow-up and use eventual recovery of ordinary ideal powers; finite colength supplies the proper affine center. The remaining mathematical work is the curve-contact-to-positivity and ordinary-power recovery argument.
-- source:
--   openai/math Ampleness stack: WeightedIdealCurveBound implies eps-ample exceptional twist, hence Serre vanishing and eventual generation of I^n by weight ≤ n(rho+eps) sections.

import Definitions.Def_OAI_PiExponent_WeightedIdealCurveCriterion
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous

open scoped BigOperators
open OAI.PiExponent.FormalInterpolation

theorem OAI.PiExponent.FormalInterpolation.curve_bound_individual_coordinate_power
    {d : Nat} (I : Ideal (MvPolynomial (Fin d) Complex))
    (hfinite : Module.Finite Complex (MvPolynomial (Fin d) Complex ⧸ I))
    (w : Fin d → Rat) (hw : ∀ i, 0 < (w i : Real))
    (rho : Rat) (hrho : 0 ≤ rho)
    (hcurve : WeightedIdealCurveBound I w rho)
    (eps : Real) (heps : 0 < eps) :
    ∀ i : Fin d, ∃ s n : Nat, 0 < s ∧ 0 < n ∧
      MvPolynomial.X i ^ n ∈ I ^ s ∧
      (n : Real) * (w i : Real) < (s : Real) * ((rho : Real) + eps) := by sorry
