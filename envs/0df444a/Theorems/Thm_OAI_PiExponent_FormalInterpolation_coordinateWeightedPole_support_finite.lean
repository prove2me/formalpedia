-- Prove2me | Theorems.Thm_OAI_PiExponent_FormalInterpolation_coordinateWeightedPole_support_finite
-- name    : OAI.PiExponent.FormalInterpolation.coordinateWeightedPole_support_finite
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-21T04:24:47.785488+00:00
-- url     : https://prove2.me/theorems/9b64e6fc-7e98-47d7-9925-187110a00e76
-- title:
--   Coordinate and weighted pole functions have finite support
-- statement:
--   Only finitely many normalized places contribute to either the selected coordinate pole sum or the weighted pole sum.

import Definitions.Def_OAI_PiExponent_WeightedIdealCurveCriterion
import Mathlib.RingTheory.Algebraic.Defs

open scoped BigOperators
open OAI.PiExponent.FormalInterpolation

theorem OAI.PiExponent.FormalInterpolation.coordinateWeightedPole_support_finite {d : Nat} (E : Type) [Field E] [Algebra Complex E] [Algebra.EssFiniteType Complex E] (htrdeg : Algebra.trdeg Complex E = 1) (x : Fin d → E) (hgen : IntermediateField.adjoin Complex (Set.range x) = ⊤) (w : Fin d → Rat) (hw : ∀ i, 0 < (w i : Real)) (k : Fin d) : Set.Finite {nu : PolynomialCurvePlace E | max (-(polynomialCurveOrder nu (x k) : Real)) 0 ≠ 0} ∧ Set.Finite {nu : PolynomialCurvePlace E | polynomialCurvePole nu x w ≠ 0} := by sorry
