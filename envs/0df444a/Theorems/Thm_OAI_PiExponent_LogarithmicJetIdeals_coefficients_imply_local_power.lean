-- Prove2me | Theorems.Thm_OAI_PiExponent_LogarithmicJetIdeals_coefficients_imply_local_power
-- name    : OAI.PiExponent.LogarithmicJetIdeals.coefficients_imply_local_power
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-14T11:27:06.559167+00:00
-- url     : https://prove2.me/theorems/a3409752-2ee9-4b22-ab6c-2cceda352f6a
-- title:
--   Weighted formal-jet coefficient vanishing implies local jet ideal powers
-- statement:
--   Under the target's positivity, common-scale, and truncation-tail hypotheses, vanishing of all formal-jet coefficients on the strict weighted simplex with padded cutoff implies membership in each center's nth local jet ideal power.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Approximation/AdmissibleMatrixGeometry.lean#L41-L44

import Definitions.Def_OAI_PiExponent_AdmissibleFormalInterpolation
import Definitions.Def_OAI_PiExponent_LogarithmicJetIdeals

open OAI.PiExponent
open OAI.PiExponent.AdmissibleFormalInterpolation
open OAI.PiExponent.LogarithmicJetIdeals

theorem OAI.PiExponent.LogarithmicJetIdeals.coefficients_imply_local_power
    {m : ℕ} (K : ℕ) (v0 theta : ℝ) (w : Fin m → ℝ) (R : ℝ)
    (r : Fin m → ℂ) (T : Fin m → ℕ) (e : Fin (m + 1) → ℕ)
    (hR : 0 < R)
    (hv : ∀ i, 0 < InterpolationMatrix.rowWeights v0 theta w i)
    (he : ∀ i, 0 < e i)
    (hscale : ∀ i, R = (e i : ℝ) * InterpolationMatrix.rowWeights v0 theta w i)
    (hT : ∀ i : Fin m,
      InterpolationMatrix.rowWeights v0 theta w i.succ ≤ (T i : ℝ) * v0)
    (n : ℕ) (P : MvPolynomial (Fin (m + 1)) ℂ)
    (hcoeff : ∀ j : Fin K, ∀ a : Fin (m + 1) → ℕ,
      a ∈ strictWeightedSimplex (InterpolationMatrix.rowWeights v0 theta w)
        (((n + m : ℕ) : ℝ) * R) →
      MvPowerSeries.coeff (InterpolationMatrix.exponentVector a)
        (AdmissibleFormalInterpolation.formalJet
          (fun i => (j.val : ℂ) * r i) P) = 0) :
    ∀ j : Fin K,
      P ∈ (localJetIdeal (fun i => (j.val : ℂ) * r i) T e) ^ n := by sorry
