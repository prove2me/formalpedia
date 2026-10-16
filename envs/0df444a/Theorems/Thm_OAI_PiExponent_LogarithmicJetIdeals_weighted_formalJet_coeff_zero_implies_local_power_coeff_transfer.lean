-- Prove2me | Theorems.Thm_OAI_PiExponent_LogarithmicJetIdeals_weighted_formalJet_coeff_zero_implies_local_power_coeff_transfer
-- name    : OAI.PiExponent.LogarithmicJetIdeals.weighted_formalJet_coeff_zero_implies_local_power_coeff_transfer
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-15T21:17:52.769666+00:00
-- url     : https://prove2.me/theorems/52122f97-569c-4aa3-9cb3-6401f4e89093
-- title:
--   Weighted formal-jet vanishing transfers to local-coordinate coefficients
-- statement:
--   Weighted formal-jet vanishing implies vanishing of local-coordinate polynomial coefficients whenever the sum of the natural-number quotients a_i/e_i is below n, under the stated positivity, scale, and truncation hypotheses.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Approximation/AdmissibleMatrixGeometry.lean#L41-L44

import Definitions.Def_OAI_PiExponent_AdmissibleFormalInterpolation
import Definitions.Def_OAI_PiExponent_LogarithmicJetIdeals
import Definitions.Def_OAI_PiExponent_LogarithmicJetIdeals_LocalCoordinates

open OAI.PiExponent
open OAI.PiExponent.AdmissibleFormalInterpolation
open OAI.PiExponent.LogarithmicJetIdeals

theorem OAI.PiExponent.LogarithmicJetIdeals.weighted_formalJet_coeff_zero_implies_local_power_coeff_transfer
    {m : ℕ} (v0 theta : ℝ) (w : Fin m → ℝ) (S : ℝ)
    (c : Fin m → ℂ) (T : Fin m → ℕ) (e : Fin (m + 1) → ℕ)
    (hS : 0 < S)
    (hv : ∀ i, 0 < InterpolationMatrix.rowWeights v0 theta w i)
    (he : ∀ i, 0 < e i)
    (hscale : ∀ i, (e i : ℝ) * InterpolationMatrix.rowWeights v0 theta w i ≤ S)
    (hT : ∀ i : Fin m,
      InterpolationMatrix.rowWeights v0 theta w i.succ ≤ (T i : ℝ) * v0)
    (n : ℕ) (P : MvPolynomial (Fin (m + 1)) ℂ)
    (hcoeff : ∀ (a : Fin (m + 1) → ℕ),
      (∑ i, InterpolationMatrix.rowWeights v0 theta w i * (a i : ℝ)) <
        ((n + m : ℕ) : ℝ) * S →
      MvPowerSeries.coeff (InterpolationMatrix.exponentVector a)
        (AdmissibleFormalInterpolation.formalJet c P) = 0) :
    ∀ a : Fin (m + 1) → ℕ,
      (∑ i, a i / e i : ℕ) < n →
      MvPolynomial.coeff (InterpolationMatrix.exponentVector a)
        (localCoordinatePolynomial c T P) = 0 := by sorry
