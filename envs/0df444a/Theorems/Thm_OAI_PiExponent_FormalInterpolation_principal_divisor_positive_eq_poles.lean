-- Prove2me | Theorems.Thm_OAI_PiExponent_FormalInterpolation_principal_divisor_positive_eq_poles
-- name    : OAI.PiExponent.FormalInterpolation.principal_divisor_positive_eq_poles
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-21T04:22:45.914168+00:00
-- url     : https://prove2.me/theorems/5172e1d9-09c0-4362-b940-4e20531a6c53
-- title:
--   Positive and negative parts of a principal divisor have equal degree
-- statement:
--   For a finite-type one-variable function field over Complex, the total positive order and total pole order of any function agree, with zero assigned order zero.

import Definitions.Def_OAI_PiExponent_TruncatedPolynomialJets
import Definitions.Def_OAI_PiExponent_LogarithmicInterpolationNumerics
import Definitions.Def_OAI_PiExponent_WeightedIdealCurveCriterion
import Mathlib.RingTheory.Algebraic.Defs

open scoped BigOperators
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction OAI.PiExponent.FormalInterpolation

theorem OAI.PiExponent.FormalInterpolation.principal_divisor_positive_eq_poles
    {E : Type} [Field E] [Algebra Complex E]
    [Algebra.EssFiniteType Complex E]
    (htrdeg : Algebra.trdeg Complex E = 1) (f : E) :
    (∑ᶠ nu : PolynomialCurvePlace E,
      max (polynomialCurveOrder nu f : Real) 0) =
      ∑ᶠ nu : PolynomialCurvePlace E,
        max (-(polynomialCurveOrder nu f : Real)) 0 := by sorry
