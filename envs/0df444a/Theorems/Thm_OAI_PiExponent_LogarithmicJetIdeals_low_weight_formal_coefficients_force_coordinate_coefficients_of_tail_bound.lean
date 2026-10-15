-- Prove2me | Theorems.Thm_OAI_PiExponent_LogarithmicJetIdeals_low_weight_formal_coefficients_force_coordinate_coefficients_of_tail_bound
-- name    : OAI.PiExponent.LogarithmicJetIdeals.low_weight_formal_coefficients_force_coordinate_coefficients_of_tail_bound
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-14T17:42:22.183619+00:00
-- url     : https://prove2.me/theorems/1539976a-e667-4a34-b975-07220c3377dc
-- title:
--   Weighted truncation preserves low-weight coefficient vanishing
-- statement:
--   For any strict weighted cutoff, if the formal logarithmic chart has zero coefficients below that cutoff, then replacing its logarithm by the coordinatewise truncations also gives zero polynomial coefficients below the cutoff, provided each truncation tail has weight at least the corresponding coordinate weight.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Approximation/AdmissibleMatrixGeometry.lean#L41-L44

import Definitions.Def_OAI_PiExponent_AdmissibleFormalInterpolation
import Definitions.Def_OAI_PiExponent_LogarithmicJetIdeals
import Definitions.Def_OAI_PiExponent_LogarithmicJetIdeals_LocalCoordinatePolynomial

open OAI.PiExponent
open OAI.PiExponent.AdmissibleFormalInterpolation
open OAI.PiExponent.LogarithmicJetIdeals
open scoped BigOperators

theorem OAI.PiExponent.LogarithmicJetIdeals.low_weight_formal_coefficients_force_coordinate_coefficients_of_tail_bound
    {m : ℕ} (v0 theta : ℝ) (w : Fin m → ℝ)
    (c : Fin m → ℂ) (T : Fin m → ℕ)
    (hv : ∀ i, 0 < InterpolationMatrix.rowWeights v0 theta w i)
    (hT : ∀ i : Fin m,
      InterpolationMatrix.rowWeights v0 theta w i.succ ≤ (T i : ℝ) * v0)
    (B : ℝ) (P : MvPolynomial (Fin (m + 1)) ℂ)
    (hcoeff : ∀ a : Fin (m + 1) → ℕ,
      (∑ i, InterpolationMatrix.rowWeights v0 theta w i * (a i : ℝ)) < B →
      MvPowerSeries.coeff (InterpolationMatrix.exponentVector a)
        (AdmissibleFormalInterpolation.formalJet c P) = 0) :
    ∀ a : Fin (m + 1) → ℕ,
      (∑ i, InterpolationMatrix.rowWeights v0 theta w i * (a i : ℝ)) < B →
      MvPolynomial.coeff (InterpolationMatrix.exponentVector a)
        (localCoordinatePolynomial c T P) = 0 := by sorry
