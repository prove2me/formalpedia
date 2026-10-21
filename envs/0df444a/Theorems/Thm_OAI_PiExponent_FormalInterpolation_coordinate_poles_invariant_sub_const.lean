-- Prove2me | Theorems.Thm_OAI_PiExponent_FormalInterpolation_coordinate_poles_invariant_sub_const
-- name    : OAI.PiExponent.FormalInterpolation.coordinate_poles_invariant_sub_const
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-21T04:23:16.802996+00:00
-- url     : https://prove2.me/theorems/3ff1d972-b04d-4823-a6b2-178e5007e830
-- title:
--   Subtracting a constant preserves coordinate pole degree
-- statement:
--   For a transcendental coordinate in a finite-type one-variable function field over Complex, subtracting any constant preserves its total pole degree.

import Definitions.Def_OAI_PiExponent_TruncatedPolynomialJets
import Definitions.Def_OAI_PiExponent_LogarithmicInterpolationNumerics
import Definitions.Def_OAI_PiExponent_WeightedIdealCurveCriterion
import Mathlib.RingTheory.Algebraic.Defs

open scoped BigOperators
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction OAI.PiExponent.FormalInterpolation

theorem OAI.PiExponent.FormalInterpolation.coordinate_poles_invariant_sub_const
    {E : Type} [Field E] [Algebra Complex E]
    [Algebra.EssFiniteType Complex E]
    (htrdeg : Algebra.trdeg Complex E = 1) (z : E)
    (hz : Transcendental Complex z) (b : Complex) :
    (∑ᶠ nu : PolynomialCurvePlace E,
      max (-(polynomialCurveOrder nu (z - algebraMap Complex E b) : Real)) 0) =
      ∑ᶠ nu : PolynomialCurvePlace E,
        max (-(polynomialCurveOrder nu z : Real)) 0 := by sorry
