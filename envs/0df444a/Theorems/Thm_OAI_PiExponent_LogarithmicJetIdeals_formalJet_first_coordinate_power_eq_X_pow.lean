-- Prove2me | Theorems.Thm_OAI_PiExponent_LogarithmicJetIdeals_formalJet_first_coordinate_power_eq_X_pow
-- name    : OAI.PiExponent.LogarithmicJetIdeals.formalJet_first_coordinate_power_eq_X_pow
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-14T10:46:07.946834+00:00
-- url     : https://prove2.me/theorems/6b1d24c1-5126-43cb-9b20-5563bca4e733
-- title:
--   The first jet coordinate maps to the corresponding power-series variable
-- statement:
--   The formal jet image of the zeroth jet coordinate raised to `n` is the zeroth power-series variable raised to `n`.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Approximation/AdmissibleMatrixGeometry.lean#L41-L44

import Definitions.Def_OAI_PiExponent_AdmissibleFormalInterpolation
import Definitions.Def_OAI_PiExponent_LogarithmicJetIdeals

open OAI.PiExponent
open OAI.PiExponent.AdmissibleFormalInterpolation
open OAI.PiExponent.LogarithmicJetIdeals
open scoped BigOperators

theorem OAI.PiExponent.LogarithmicJetIdeals.formalJet_first_coordinate_power_eq_X_pow
    {m : ℕ} (c : Fin m → ℂ) (T : Fin m → ℕ)
    (n : ℕ) :
    AdmissibleFormalInterpolation.formalJet c
      (jetCoordinate c T (0 : Fin (m + 1)) ^ n) =
        MvPowerSeries.X (0 : Fin (m + 1)) ^ n := by sorry
