-- Prove2me | Theorems.Thm_OAI_PiExponent_FormalInterpolation_coordinate_pole_divisor_le_weighted
-- name    : OAI.PiExponent.FormalInterpolation.coordinate_pole_divisor_le_weighted
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-21T03:48:38.54557+00:00
-- url     : https://prove2.me/theorems/728158a9-62c2-4318-be6a-ccf9636ffe43
-- title:
--   Coordinate pole divisor is bounded by weighted curve poles
-- statement:
--   For positive coordinate weights, the total pole order of any chosen coordinate is at most its weight times the total weighted pole quantity. At each place this follows from the coordinate's entry in the supremum defining `polynomialCurvePole`, together with its zero entry; the proof must establish the finite-support facts needed for the `finsum` comparison.

import Definitions.Def_OAI_PiExponent_TruncatedPolynomialJets
import Definitions.Def_OAI_PiExponent_LogarithmicInterpolationNumerics
import Definitions.Def_OAI_PiExponent_WeightedIdealCurveCriterion
import Mathlib.RingTheory.Algebraic.Defs

open scoped BigOperators
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction OAI.PiExponent.FormalInterpolation

theorem OAI.PiExponent.FormalInterpolation.coordinate_pole_divisor_le_weighted
    {d : Nat} (E : Type) [Field E] [Algebra Complex E]
    [Algebra.EssFiniteType Complex E]
    (htrdeg : Algebra.trdeg Complex E = 1) (x : Fin d → E)
    (hgen : IntermediateField.adjoin Complex (Set.range x) = ⊤)
    (w : Fin d → Rat) (hw : ∀ i, 0 < (w i : Real)) (k : Fin d) :
    (∑ᶠ nu : PolynomialCurvePlace E,
      max (-(polynomialCurveOrder nu (x k) : Real)) 0) ≤
      (w k : Real) *
        (∑ᶠ nu : PolynomialCurvePlace E, polynomialCurvePole nu x w) := by sorry
