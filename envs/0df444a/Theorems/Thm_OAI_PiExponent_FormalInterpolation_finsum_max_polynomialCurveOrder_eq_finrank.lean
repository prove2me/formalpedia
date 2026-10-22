-- Prove2me | Theorems.Thm_OAI_PiExponent_FormalInterpolation_finsum_max_polynomialCurveOrder_eq_finrank
-- name    : OAI.PiExponent.FormalInterpolation.finsum_max_polynomialCurveOrder_eq_finrank
-- status  : Proved
-- author  : @Ethan Cheung
-- created : 2026-10-21T06:16:44.941229+00:00
-- url     : https://prove2.me/theorems/2870a9a4-c484-48e5-b213-d27657a8e2d0
-- title:
--   Zero mass of a transcendental equals $[E:\mathbb{C}(x)]$
-- statement:
--   Under the same hypotheses as the pole-mass companion, the finsum of $\max(\operatorname{ord}_\nu(x),0)$ over polynomial curve places equals $[E:\mathbb{C}(x)]$. Together with the pole identity this yields $\sum \max(\operatorname{ord},0)=\sum \max(-\operatorname{ord},0)$ for transcendental elements.
-- source:
--   Mission d7ce6393 FormalInterpolation AG chain; cf. AlgebraicCurve.exists_finset_sum_ord_sub_algebraMap_eq_finrank_of_isAlgClosed with a=0

import Definitions.Def_OAI_PiExponent_WeightedIdealCurveCriterion
import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.RingTheory.Algebraic.Defs

open scoped BigOperators
open IntermediateField
open OAI.PiExponent.FormalInterpolation
open AlgebraicCurve

theorem OAI.PiExponent.FormalInterpolation.finsum_max_polynomialCurveOrder_eq_finrank
    {E : Type} [Field E] [Algebra Complex E]
    (x : E) (hx : Transcendental Complex x)
    (hfin : FiniteDimensional (IntermediateField.adjoin Complex ({x} : Set E)) E) :
    (∑ᶠ nu : PolynomialCurvePlace E,
      max (polynomialCurveOrder nu x : Real) 0) =
      (Module.finrank (IntermediateField.adjoin Complex ({x} : Set E)) E : Real) := by sorry
