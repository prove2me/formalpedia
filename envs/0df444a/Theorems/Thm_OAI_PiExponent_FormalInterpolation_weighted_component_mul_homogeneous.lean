-- Prove2me | Theorems.Thm_OAI_PiExponent_FormalInterpolation_weighted_component_mul_homogeneous
-- name    : OAI.PiExponent.FormalInterpolation.weighted_component_mul_homogeneous
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-23T08:20:06.851238+00:00
-- url     : https://prove2.me/theorems/a032a210-14ce-4f83-9e20-804be797c50f
-- title:
--   Weighted component of a product with a homogeneous factor
-- statement:
--   For any polynomial `a` and degree-D weighted homogeneous polynomial `g`, the degree-E component of `a * g` equals the degree-(E−D) component of `a`, multiplied by `g`. No positivity or nonzero assumptions are needed. This is the product identity that lets the parent extract homogeneous coefficients.
-- source:
--   openai/math Ampleness stack: WeightedIdealCurveBound implies eps-ample exceptional twist, hence Serre vanishing and eventual generation of I^n by weight ≤ n(rho+eps) sections.

import Mathlib.Data.Complex.Basic
import Mathlib.RingTheory.Ideal.Quotient.Basic
import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous

theorem OAI.PiExponent.FormalInterpolation.weighted_component_mul_homogeneous
    {d : Nat} (w : Fin d → Rat) (D E : Real)
    (a g : MvPolynomial (Fin d) Complex)
    (hg : g.IsWeightedHomogeneous (fun i => (w i : Real)) D) :
    MvPolynomial.weightedHomogeneousComponent (fun i => (w i : Real)) E (a * g) =
      MvPolynomial.weightedHomogeneousComponent (fun i => (w i : Real)) (E - D) a * g := by sorry
