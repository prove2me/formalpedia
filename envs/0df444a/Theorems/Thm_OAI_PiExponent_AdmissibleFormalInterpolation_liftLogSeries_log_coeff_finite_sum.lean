-- Prove2me | Theorems.Thm_OAI_PiExponent_AdmissibleFormalInterpolation_liftLogSeries_log_coeff_finite_sum
-- name    : OAI.PiExponent.AdmissibleFormalInterpolation.liftLogSeries_log_coeff_finite_sum
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-16T12:07:46.691619+00:00
-- url     : https://prove2.me/theorems/7844c2a5-cd4d-420c-80b5-4e6a3f71daa0
-- title:
--   Lifted formal logarithm agrees with its finite sum below the cutoff
-- statement:
--   The lifted logarithm and its finite logarithmic sum have equal coefficients whenever the first-coordinate exponent is strictly below the cutoff. Both have zero coefficients involving later variables, and their constant coefficients vanish.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Approximation/AdmissibleMatrixGeometry.lean#L41-L44

import Definitions.Def_OAI_PiExponent_AdmissibleFormalInterpolation

open scoped BigOperators
open OAI.PiExponent.AdmissibleFormalInterpolation

theorem OAI.PiExponent.AdmissibleFormalInterpolation.liftLogSeries_log_coeff_finite_sum
    {m : ℕ} (T : ℕ) (a : Fin (m + 1) →₀ ℕ) (ha : a 0 < T) :
    MvPowerSeries.coeff a (liftLogSeries m (PowerSeries.log ℂ)) =
      MvPowerSeries.coeff a
        (∑ k ∈ Finset.range T,
          (if k = 0 then 0 else
            (((-1 : ℂ) ^ (k + 1)) / (k : ℂ)) •
              (MvPowerSeries.X 0 : MvPowerSeries (Fin (m + 1)) ℂ) ^ k)) := by sorry
