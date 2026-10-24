-- Prove2me | Theorems.Thm_OAI_PiExponent_FormalInterpolation_quotient_algebraMap_smul
-- name    : OAI.PiExponent.FormalInterpolation.quotient_algebraMap_smul
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-23T13:19:53.836557+00:00
-- url     : https://prove2.me/theorems/27dc44fb-a9f0-4822-88f7-e72f3ebd7a84
-- title:
--   Scalar multiplication in an ideal quotient
-- statement:
--   For a complex algebra and an ideal quotient with compatible complex and ring-module actions, quotienting a product by a scalar is the same as scalar multiplication in the quotient. This lets the parent translate each polynomial coefficient product into the scalar action used by the powers-dependence child.
-- source:
--   openai/math Ampleness stack: WeightedIdealCurveBound implies eps-ample exceptional twist, hence Serre vanishing and eventual generation of I^n by weight ≤ n(rho+eps) sections.

import Mathlib.Data.Complex.Basic
import Mathlib.RingTheory.Ideal.Quotient.Basic

theorem OAI.PiExponent.FormalInterpolation.quotient_algebraMap_smul
    {R : Type*} [CommRing R] [Algebra ℂ R] (I : Ideal R)
    [Module R (R ⧸ I)] [Module ℂ (R ⧸ I)]
    [IsScalarTower ℂ R (R ⧸ I)] (c : ℂ) (p : R) :
    Ideal.Quotient.mk I (algebraMap ℂ R c * p) =
      c • Ideal.Quotient.mk I p := by sorry
