-- Prove2me | Theorems.Thm_OAI_PiExponent_AdmissibleFormalInterpolation_coordinate_X_support_bound
-- name    : OAI.PiExponent.AdmissibleFormalInterpolation.coordinate_X_support_bound
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-16T05:52:20.573018+00:00
-- url     : https://prove2.me/theorems/4590ce3b-e0d7-45ba-a3e9-533d09b1bfe6
-- title:
--   Coordinate variables have coordinate support
-- statement:
--   If a coefficient of a multivariate coordinate variable is nonzero, the exponent vector is supported at that coordinate with exponent one, so its weighted degree equals the weight of that coordinate.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Approximation/AdmissibleMatrixGeometry.lean#L41-L44

import Definitions.Def_OAI_PiExponent_AdmissibleFormalInterpolation
import Mathlib.RingTheory.MvPowerSeries.Substitution

open scoped BigOperators
open OAI.PiExponent
open OAI.PiExponent.AdmissibleFormalInterpolation

theorem OAI.PiExponent.AdmissibleFormalInterpolation.coordinate_X_support_bound
    {m : ℕ} (q : Fin (m + 1) → ℝ) (a : Fin (m + 1) → ℕ)
    (r : Fin (m + 1)) :
    MvPowerSeries.coeff (InterpolationMatrix.exponentVector a)
      (MvPowerSeries.X r) ≠ 0 →
    q r ≤ ∑ j, q j * (a j : ℝ) := by sorry
