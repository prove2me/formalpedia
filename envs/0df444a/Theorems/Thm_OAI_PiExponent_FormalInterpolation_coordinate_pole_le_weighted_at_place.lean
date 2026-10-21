-- Prove2me | Theorems.Thm_OAI_PiExponent_FormalInterpolation_coordinate_pole_le_weighted_at_place
-- name    : OAI.PiExponent.FormalInterpolation.coordinate_pole_le_weighted_at_place
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-21T04:24:37.959281+00:00
-- url     : https://prove2.me/theorems/e728176d-73d3-4b06-b8e3-f5b4d4ab6246
-- title:
--   A coordinate pole is bounded at each place
-- statement:
--   At each place, the selected coordinate's nonnegative pole order is bounded by its positive weight times the weighted pole supremum.

import Definitions.Def_OAI_PiExponent_WeightedIdealCurveCriterion

open scoped BigOperators
open OAI.PiExponent.FormalInterpolation

theorem OAI.PiExponent.FormalInterpolation.coordinate_pole_le_weighted_at_place {d : Nat} {E : Type} [Field E] [Algebra Complex E] (x : Fin d → E) (w : Fin d → Rat) (hw : ∀ i, 0 < (w i : Real)) (k : Fin d) : ∀ nu : PolynomialCurvePlace E, 0 ≤ max (-(polynomialCurveOrder nu (x k) : Real)) 0 ∧ max (-(polynomialCurveOrder nu (x k) : Real)) 0 ≤ (w k : Real) * polynomialCurvePole nu x w := by sorry
