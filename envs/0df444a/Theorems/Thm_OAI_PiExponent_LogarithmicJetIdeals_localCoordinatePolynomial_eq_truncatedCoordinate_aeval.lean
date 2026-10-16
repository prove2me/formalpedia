-- Prove2me | Theorems.Thm_OAI_PiExponent_LogarithmicJetIdeals_localCoordinatePolynomial_eq_truncatedCoordinate_aeval
-- name    : OAI.PiExponent.LogarithmicJetIdeals.localCoordinatePolynomial_eq_truncatedCoordinate_aeval
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-16T05:49:11.137547+00:00
-- url     : https://prove2.me/theorems/6d78b1c5-cf8c-4217-8ca3-1aa61c86de83
-- title:
--   Local-coordinate polynomial embeds as evaluation at truncated-log coordinates
-- statement:
--   The polynomial defining the local coordinates, when embedded into multivariate power series, is evaluation at the same truncated-log coordinates.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Approximation/AdmissibleMatrixGeometry.lean#L41-L44

import Definitions.Def_OAI_PiExponent_LogarithmicJetIdeals_LocalCoordinates
import Mathlib.RingTheory.MvPowerSeries.Substitution

open OAI.PiExponent
open OAI.PiExponent.AdmissibleFormalInterpolation
open OAI.PiExponent.LogarithmicJetIdeals

theorem OAI.PiExponent.LogarithmicJetIdeals.localCoordinatePolynomial_eq_truncatedCoordinate_aeval
    {m : ℕ} (c : Fin m → ℂ) (T : Fin m → ℕ)
    (P : MvPolynomial (Fin (m + 1)) ℂ) :
    (localCoordinatePolynomial c T P : MvPowerSeries (Fin (m + 1)) ℂ) =
      MvPolynomial.aeval
        (Fin.cases (1 + MvPowerSeries.X 0)
          (fun i : Fin m => MvPowerSeries.C (c i) + MvPowerSeries.X i.succ +
            liftLogSeries m (InterpolationMatrix.truncatedLog (T i) : PowerSeries ℂ))) P := by sorry
