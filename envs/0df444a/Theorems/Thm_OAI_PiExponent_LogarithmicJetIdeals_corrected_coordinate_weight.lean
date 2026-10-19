-- Prove2me | Theorems.Thm_OAI_PiExponent_LogarithmicJetIdeals_corrected_coordinate_weight
-- name    : OAI.PiExponent.LogarithmicJetIdeals.corrected_coordinate_weight
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-16T21:39:33.743425+00:00
-- url     : https://prove2.me/theorems/a9e74de4-04ef-4d50-b1ab-e014f605f632
-- title:
--   Corrected shear coordinate coefficients meet their weight
-- statement:
--   For each corrected coordinate, every nonzero coefficient has weight at least the coordinate weight. The proof must account for the disjoint monomial supports of the explicit variable and the lifted one-variable correction series, then use the strict cutoff to bound every surviving correction term, including the equality boundary.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Approximation/AdmissibleMatrixGeometry.lean#L41-L44

import Definitions.Def_OAI_PiExponent_AdmissibleFormalInterpolation
import Definitions.Def_OAI_PiExponent_LogarithmicJetIdeals_LocalCoordinatePolynomial

open OAI.PiExponent
open OAI.PiExponent.AdmissibleFormalInterpolation
open scoped BigOperators

theorem OAI.PiExponent.LogarithmicJetIdeals.corrected_coordinate_weight
    {m : ℕ} (q : Fin (m + 1) → ℝ) (hq : ∀ j, 0 < q j)
    (D : Fin m → PowerSeries ℂ)
    (hD : ∀ i : Fin m, ∀ n : ℕ,
      (n : ℝ) * q 0 < q i.succ → PowerSeries.coeff n (D i) = 0)
    (i : Fin m) (b : Fin (m + 1) →₀ ℕ) :
    MvPowerSeries.coeff b
      (MvPowerSeries.X i.succ - liftLogSeries m (D i)) ≠ 0 →
      q i.succ ≤ ∑ j, q j * (b j : ℝ) := by sorry
