-- Prove2me | Theorems.Thm_OAI_PiExponent_LogarithmicJetIdeals_polynomial_series_coordinate_change_factorization
-- name    : OAI.PiExponent.LogarithmicJetIdeals.polynomial_series_coordinate_change_factorization
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-14T20:39:31.547655+00:00
-- url     : https://prove2.me/theorems/3d0781f1-6328-4bff-b81c-53056685d34b
-- title:
--   Formal coordinate evaluation factors through polynomial corrections and a triangular shear
-- statement:
--   Evaluating a polynomial in coordinates with arbitrary series corrections factors as evaluation using arbitrary polynomial corrections followed by a triangular shear adding their series differences.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Approximation/AdmissibleMatrixGeometry.lean#L41-L44

import Definitions.Def_OAI_PiExponent_AdmissibleFormalInterpolation
import Definitions.Def_OAI_PiExponent_LogarithmicJetIdeals_LocalCoordinatePolynomial

open OAI.PiExponent
open OAI.PiExponent.AdmissibleFormalInterpolation
open scoped BigOperators

theorem OAI.PiExponent.LogarithmicJetIdeals.polynomial_series_coordinate_change_factorization
    {m : ℕ} (c : Fin m → ℂ) (G : Fin m → PowerSeries ℂ)
    (H : Fin m → Polynomial ℂ) (P : MvPolynomial (Fin (m + 1)) ℂ) :
    MvPolynomial.aeval
      (Fin.cases (MvPowerSeries.X 0)
        (fun i => MvPowerSeries.X i.succ +
          liftLogSeries m (G i - (H i : PowerSeries ℂ))))
      (MvPolynomial.aeval
        (Fin.cases (1 + MvPolynomial.X 0)
          (fun i => MvPolynomial.C (c i) + MvPolynomial.X i.succ +
            Polynomial.eval₂ MvPolynomial.C (MvPolynomial.X 0) (H i))) P) =
    MvPolynomial.aeval
      (Fin.cases (1 + MvPowerSeries.X 0)
        (fun i => MvPowerSeries.C (c i) + MvPowerSeries.X i.succ +
          liftLogSeries m (G i))) P := by sorry
