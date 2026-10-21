-- Prove2me | Theorems.Thm_OAI_PiExponent_LogarithmicJetIdeals_low_weight_formal_coefficients_force_coordinate_coefficients
-- name    : OAI.PiExponent.LogarithmicJetIdeals.low_weight_formal_coefficients_force_coordinate_coefficients
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-14T13:47:14.732239+00:00
-- url     : https://prove2.me/theorems/55786407-165e-4873-9a54-e1beb7b21af4
-- title:
--   Formal coefficient vanishing forces truncated-coordinate coefficient vanishing
-- statement:
--   Under the positive weight, scale, and truncation-tail hypotheses, vanishing of the formal-chart coefficients below $(n+m)R$ implies vanishing of the truncated-coordinate polynomial coefficients below the same strict cutoff.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Approximation/AdmissibleMatrixGeometry.lean#L41-L44

import Definitions.Def_OAI_PiExponent_AdmissibleFormalInterpolation
import Definitions.Def_OAI_PiExponent_LogarithmicJetIdeals
import Definitions.Def_OAI_PiExponent_LogarithmicJetIdeals_LocalCoordinatePolynomial

open OAI.PiExponent
open OAI.PiExponent.AdmissibleFormalInterpolation
open OAI.PiExponent.LogarithmicJetIdeals
open scoped BigOperators

theorem OAI.PiExponent.LogarithmicJetIdeals.low_weight_formal_coefficients_force_coordinate_coefficients
    {m : ℕ} (v0 theta : ℝ) (w : Fin m → ℝ) (R : ℝ)
    (c : Fin m → ℂ) (T : Fin m → ℕ) (e : Fin (m + 1) → ℕ)
    (hR : 0 < R)
    (hv : ∀ i, 0 < InterpolationMatrix.rowWeights v0 theta w i)
    (he : ∀ i, 0 < e i)
    (hscale : ∀ i, R = (e i : ℝ) * InterpolationMatrix.rowWeights v0 theta w i)
    (hT : ∀ i : Fin m,
      InterpolationMatrix.rowWeights v0 theta w i.succ ≤ (T i : ℝ) * v0)
    (n : ℕ) (P : MvPolynomial (Fin (m + 1)) ℂ)
    (hcoeff : ∀ a : Fin (m + 1) → ℕ,
      (∑ i, InterpolationMatrix.rowWeights v0 theta w i * (a i : ℝ)) <
        (((n + m : ℕ) : ℝ) * R) →
      MvPowerSeries.coeff (InterpolationMatrix.exponentVector a)
        (AdmissibleFormalInterpolation.formalJet c P) = 0) :
    ∀ a : Fin (m + 1) → ℕ,
      (∑ i, InterpolationMatrix.rowWeights v0 theta w i * (a i : ℝ)) <
        (((n + m : ℕ) : ℝ) * R) →
      MvPolynomial.coeff (InterpolationMatrix.exponentVector a)
        (localCoordinatePolynomial c T P) = 0 := by sorry
