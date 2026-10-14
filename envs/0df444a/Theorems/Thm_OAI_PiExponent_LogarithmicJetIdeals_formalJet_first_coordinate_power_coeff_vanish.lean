-- Prove2me | Theorems.Thm_OAI_PiExponent_LogarithmicJetIdeals_formalJet_first_coordinate_power_coeff_vanish
-- name    : OAI.PiExponent.LogarithmicJetIdeals.formalJet_first_coordinate_power_coeff_vanish
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-14T09:59:38.17398+00:00
-- url     : https://prove2.me/theorems/71018b2f-831f-4dfa-a3c7-0465adab6534
-- title:
--   First jet power has no coefficients below its exponent
-- statement:
--   For any center data and truncation orders, the formal jet image of the zeroth jet coordinate raised to n has zero coefficient at exponent vectors whose zeroth exponent is strictly below n. The strict cutoff is essential; the lemma makes no claim at or above n.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Approximation/AdmissibleMatrixGeometry.lean#L41-L44

import Definitions.Def_OAI_PiExponent_AdmissibleFormalInterpolation
import Definitions.Def_OAI_PiExponent_LogarithmicJetIdeals

open OAI.PiExponent
open OAI.PiExponent.AdmissibleFormalInterpolation
open OAI.PiExponent.LogarithmicJetIdeals
open scoped BigOperators

theorem OAI.PiExponent.LogarithmicJetIdeals.formalJet_first_coordinate_power_coeff_vanish
    {m : ℕ} (c : Fin m → ℂ) (T : Fin m → ℕ)
    (b : Fin (m + 1) → ℕ) (n : ℕ)
    (hbn : b (0 : Fin (m + 1)) < n) :
    MvPowerSeries.coeff (InterpolationMatrix.exponentVector b)
      (AdmissibleFormalInterpolation.formalJet c
        (jetCoordinate c T (0 : Fin (m + 1)) ^ n)) = 0 := by sorry
