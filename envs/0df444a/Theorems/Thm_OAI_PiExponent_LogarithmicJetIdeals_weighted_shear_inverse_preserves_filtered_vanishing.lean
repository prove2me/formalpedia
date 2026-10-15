-- Prove2me | Theorems.Thm_OAI_PiExponent_LogarithmicJetIdeals_weighted_shear_inverse_preserves_filtered_vanishing
-- name    : OAI.PiExponent.LogarithmicJetIdeals.weighted_shear_inverse_preserves_filtered_vanishing
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-14T22:33:56.289881+00:00
-- url     : https://prove2.me/theorems/2246a5c5-ed0e-4788-b9ef-2fcb7ce76f3d
-- title:
--   Inverse triangular substitution preserves weighted coefficient vanishing
-- statement:
--   If a multivariate formal power series has no coefficients below a strict positive weighted cutoff, then substituting each affected variable by itself minus a one-variable series of at least that variable’s weight preserves the vanishing.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Approximation/AdmissibleMatrixGeometry.lean#L41-L44

import Definitions.Def_OAI_PiExponent_AdmissibleFormalInterpolation
import Definitions.Def_OAI_PiExponent_LogarithmicJetIdeals_LocalCoordinatePolynomial

open OAI.PiExponent
open OAI.PiExponent.AdmissibleFormalInterpolation
open scoped BigOperators

theorem OAI.PiExponent.LogarithmicJetIdeals.weighted_shear_inverse_preserves_filtered_vanishing
    {m : ℕ} (q : Fin (m + 1) → ℝ) (hq : ∀ j, 0 < q j)
    (D : Fin m → PowerSeries ℂ)
    (hD : ∀ i : Fin m, ∀ n : ℕ,
      (n : ℝ) * q 0 < q i.succ → PowerSeries.coeff n (D i) = 0)
    (B : ℝ) (F : MvPowerSeries (Fin (m + 1)) ℂ)
    (hF : ∀ a : Fin (m + 1) → ℕ,
      (∑ j, q j * (a j : ℝ)) < B →
      MvPowerSeries.coeff (InterpolationMatrix.exponentVector a) F = 0) :
    ∀ a : Fin (m + 1) → ℕ,
      (∑ j, q j * (a j : ℝ)) < B →
      MvPowerSeries.coeff (InterpolationMatrix.exponentVector a)
        (MvPowerSeries.subst
          (Fin.cases (MvPowerSeries.X 0)
            (fun i => MvPowerSeries.X i.succ - liftLogSeries m (D i))) F) = 0 := by sorry
