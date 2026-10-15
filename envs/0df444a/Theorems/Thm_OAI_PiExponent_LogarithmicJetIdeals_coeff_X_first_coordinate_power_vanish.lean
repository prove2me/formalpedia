-- Prove2me | Theorems.Thm_OAI_PiExponent_LogarithmicJetIdeals_coeff_X_first_coordinate_power_vanish
-- name    : OAI.PiExponent.LogarithmicJetIdeals.coeff_X_first_coordinate_power_vanish
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-14T10:46:47.852806+00:00
-- url     : https://prove2.me/theorems/813fdf92-d4de-4309-a700-475d23d8b146
-- title:
--   A monomial has no coefficients below its first-coordinate degree
-- statement:
--   The coefficient of the explicitly typed zeroth variable power vanishes at exponent vectors whose zeroth coordinate is strictly less than the power.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Approximation/AdmissibleMatrixGeometry.lean#L41-L44

import Definitions.Def_OAI_PiExponent_AdmissibleFormalInterpolation
import Definitions.Def_OAI_PiExponent_LogarithmicJetIdeals

open OAI.PiExponent
open OAI.PiExponent.AdmissibleFormalInterpolation
open OAI.PiExponent.LogarithmicJetIdeals
open scoped BigOperators

theorem OAI.PiExponent.LogarithmicJetIdeals.coeff_X_first_coordinate_power_vanish
    {m : ℕ} (b : Fin (m + 1) → ℕ) (n : ℕ)
    (hbn : b (0 : Fin (m + 1)) < n) :
    MvPowerSeries.coeff (InterpolationMatrix.exponentVector b)
      ((MvPowerSeries.X (0 : Fin (m + 1)) :
        MvPowerSeries (Fin (m + 1)) ℂ) ^ n) = 0 := by sorry
