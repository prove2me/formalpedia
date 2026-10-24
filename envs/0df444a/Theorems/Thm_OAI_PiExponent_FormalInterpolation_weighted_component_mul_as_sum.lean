-- Prove2me | Theorems.Thm_OAI_PiExponent_FormalInterpolation_weighted_component_mul_as_sum
-- name    : OAI.PiExponent.FormalInterpolation.weighted_component_mul_as_sum
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-23T06:25:40.567636+00:00
-- url     : https://prove2.me/theorems/a3e8d500-fe57-4f24-b3fa-2058ff02a443
-- title:
--   Weighted component of a product as a finite sum
-- statement:
--   The degree-`E` component of `q * f` is the finite sum of the degree-`a` components of `q` multiplied by `f`, over weights in the support of `q` together with `E - D`; only weights satisfying `a + D = E` contribute.
-- source:
--   openai/math Ampleness stack: WeightedIdealCurveBound implies eps-ample exceptional twist, hence Serre vanishing and eventual generation of I^n by weight ≤ n(rho+eps) sections.

import Mathlib.Data.Complex.Basic
import Mathlib.RingTheory.Adjoin.Basic
import Mathlib.RingTheory.Finiteness.Defs
import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous

open scoped BigOperators

theorem OAI.PiExponent.FormalInterpolation.weighted_component_mul_as_sum
    {d : Nat} (w : Fin d → Real) (D E : Real)
    (q f : MvPolynomial (Fin d) Complex)
    (hf : MvPolynomial.IsWeightedHomogeneous w f D) :
    MvPolynomial.weightedHomogeneousComponent w E (q * f) =
      ∑ a ∈ insert (E - D) (q.support.image (Finsupp.weight w)),
        if a + D = E then
          MvPolynomial.weightedHomogeneousComponent w a q * f
        else 0 := by sorry
