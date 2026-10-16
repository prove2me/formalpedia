-- Prove2me | Theorems.Thm_OAI_PiExponent_LogarithmicJetIdeals_liftLogSeries_coeff_truncation
-- name    : OAI.PiExponent.LogarithmicJetIdeals.liftLogSeries_coeff_truncation
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-15T05:41:32.656142+00:00
-- url     : https://prove2.me/theorems/d49230b8-4c14-40e6-ab28-9b39557a0bff
-- title:
--   Explicit finite truncation preserves coefficients of a lifted univariate series
-- statement:
--   Lifting any univariate complex power series into the distinguished variable agrees with its explicit polynomial truncation at every multi-index whose distinguished coordinate is strictly below the cutoff.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Approximation/AdmissibleMatrixGeometry.lean#L41-L44

import Definitions.Def_OAI_PiExponent_AdmissibleFormalInterpolation

open scoped BigOperators
open OAI.PiExponent.AdmissibleFormalInterpolation

theorem OAI.PiExponent.LogarithmicJetIdeals.liftLogSeries_coeff_truncation
    (m : ℕ) (f : PowerSeries ℂ) (T : ℕ)
    (d : Fin (m + 1) → ℕ) (hd : d 0 < T) :
    MvPowerSeries.coeff (Finsupp.equivFunOnFinite.symm d) (liftLogSeries m f) =
      MvPowerSeries.coeff (Finsupp.equivFunOnFinite.symm d)
        (∑ n ∈ Finset.range T,
          MvPowerSeries.C (PowerSeries.coeff n f) *
            (MvPowerSeries.X (0 : Fin (m + 1))) ^ n) := by sorry
