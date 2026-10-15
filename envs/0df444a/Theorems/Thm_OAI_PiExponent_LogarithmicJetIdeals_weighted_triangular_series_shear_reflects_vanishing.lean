-- Prove2me | Theorems.Thm_OAI_PiExponent_LogarithmicJetIdeals_weighted_triangular_series_shear_reflects_vanishing
-- name    : OAI.PiExponent.LogarithmicJetIdeals.weighted_triangular_series_shear_reflects_vanishing
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-14T20:39:02.937067+00:00
-- url     : https://prove2.me/theorems/8b0bd1ff-d1c9-41c7-a248-4140383438e4
-- title:
--   Weighted triangular series shears reflect filtered coefficient vanishing
-- statement:
--   For positive coordinate weights, a triangular shear adding one-variable series whose terms have at least the weight of the affected coordinate reflects vanishing of polynomial coefficients below any strict weighted cutoff.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Approximation/AdmissibleMatrixGeometry.lean#L41-L44

import Definitions.Def_OAI_PiExponent_AdmissibleFormalInterpolation
import Definitions.Def_OAI_PiExponent_LogarithmicJetIdeals_LocalCoordinatePolynomial

open OAI.PiExponent
open OAI.PiExponent.AdmissibleFormalInterpolation
open scoped BigOperators

theorem OAI.PiExponent.LogarithmicJetIdeals.weighted_triangular_series_shear_reflects_vanishing
    {m : ℕ} (q : Fin (m + 1) → ℝ) (hq : ∀ j, 0 < q j)
    (D : Fin m → PowerSeries ℂ)
    (hD : ∀ i : Fin m, ∀ n : ℕ,
      (n : ℝ) * q 0 < q i.succ → PowerSeries.coeff n (D i) = 0)
    (B : ℝ) (Q : MvPolynomial (Fin (m + 1)) ℂ)
    (hcoeff : ∀ a : Fin (m + 1) → ℕ,
      (∑ j, q j * (a j : ℝ)) < B →
      MvPowerSeries.coeff (InterpolationMatrix.exponentVector a)
        (MvPolynomial.aeval
          (Fin.cases (MvPowerSeries.X 0)
            (fun i => MvPowerSeries.X i.succ + liftLogSeries m (D i))) Q) = 0) :
    ∀ a : Fin (m + 1) → ℕ,
      (∑ j, q j * (a j : ℝ)) < B →
      MvPolynomial.coeff (InterpolationMatrix.exponentVector a) Q = 0 := by sorry
