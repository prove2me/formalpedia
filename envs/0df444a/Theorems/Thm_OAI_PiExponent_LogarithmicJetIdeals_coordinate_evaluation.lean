-- Prove2me | Theorems.Thm_OAI_PiExponent_LogarithmicJetIdeals_coordinate_evaluation
-- name    : OAI.PiExponent.LogarithmicJetIdeals.coordinate_evaluation
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-14T21:52:03.6569+00:00
-- url     : https://prove2.me/theorems/44986c32-62bf-41e4-be98-99bd91034eb6
-- title:
--   Triangular shear evaluates each polynomial-corrected coordinate
-- statement:
--   For every coordinate, evaluating its polynomial-corrected value under the triangular shear gives the value with the full power-series correction.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Approximation/AdmissibleMatrixGeometry.lean#L41-L44

import Definitions.Def_OAI_PiExponent_AdmissibleFormalInterpolation
import Definitions.Def_OAI_PiExponent_LogarithmicJetIdeals_LocalCoordinatePolynomial

open OAI.PiExponent
open OAI.PiExponent.AdmissibleFormalInterpolation
open scoped BigOperators

theorem OAI.PiExponent.LogarithmicJetIdeals.coordinate_evaluation
    {m : ℕ} (c : Fin m → ℂ) (G : Fin m → PowerSeries ℂ)
    (H : Fin m → Polynomial ℂ) (i : Fin (m + 1)) :
    MvPolynomial.aeval
      (Fin.cases (MvPowerSeries.X (0 : Fin (m + 1)))
        (fun j => MvPowerSeries.X j.succ +
          liftLogSeries m (G j - (H j : PowerSeries ℂ))) :
        Fin (m + 1) → MvPowerSeries (Fin (m + 1)) ℂ)
      ((Fin.cases (1 + MvPolynomial.X (0 : Fin (m + 1)))
        (fun j => MvPolynomial.C (c j) + MvPolynomial.X j.succ +
          Polynomial.eval₂ MvPolynomial.C (MvPolynomial.X 0) (H j)) :
        Fin (m + 1) → MvPolynomial (Fin (m + 1)) ℂ) i) =
    Fin.cases (1 + MvPowerSeries.X (0 : Fin (m + 1)))
      (fun j => MvPowerSeries.C (c j) + MvPowerSeries.X j.succ +
        liftLogSeries m (G j)) i := by sorry
