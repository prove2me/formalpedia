-- Prove2me | Theorems.Thm_OAI_PiExponent_LogarithmicJetIdeals_weighted_shear_coordinate_coefficients
-- name    : OAI.PiExponent.LogarithmicJetIdeals.weighted_shear_coordinate_coefficients
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-16T19:23:27.976919+00:00
-- url     : https://prove2.me/theorems/ccaac5e2-abb9-495e-b341-ca07ee53016e
-- title:
--   Shear coordinates have no terms below their assigned weights
-- statement:
--   The coefficient cutoff on each correction series ensures that every nonzero coefficient of each inverse shear coordinate has weight at least its assigned coordinate weight, including equality at the boundary.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Approximation/AdmissibleMatrixGeometry.lean#L41-L44

import Definitions.Def_OAI_PiExponent_AdmissibleFormalInterpolation
import Definitions.Def_OAI_PiExponent_LogarithmicJetIdeals_LocalCoordinatePolynomial

open OAI.PiExponent
open OAI.PiExponent.AdmissibleFormalInterpolation
open scoped BigOperators

theorem OAI.PiExponent.LogarithmicJetIdeals.weighted_shear_coordinate_coefficients
    {m : ℕ} (q : Fin (m + 1) → ℝ) (hq : ∀ j, 0 < q j)
    (D : Fin m → PowerSeries ℂ)
    (hD : ∀ i : Fin m, ∀ n : ℕ,
      (n : ℝ) * q 0 < q i.succ → PowerSeries.coeff n (D i) = 0) :
    ∀ i : Fin (m + 1), ∀ b : Fin (m + 1) →₀ ℕ,
      MvPowerSeries.coeff b
        (Fin.cases (MvPowerSeries.X 0)
          (fun i => MvPowerSeries.X i.succ - liftLogSeries m (D i)) i) ≠ 0 →
      q i ≤ ∑ j, q j * (b j : ℝ) := by sorry
