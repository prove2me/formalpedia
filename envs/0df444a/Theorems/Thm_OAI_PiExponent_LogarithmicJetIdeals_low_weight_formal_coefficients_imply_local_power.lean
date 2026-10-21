-- Prove2me | Theorems.Thm_OAI_PiExponent_LogarithmicJetIdeals_low_weight_formal_coefficients_imply_local_power
-- name    : OAI.PiExponent.LogarithmicJetIdeals.low_weight_formal_coefficients_imply_local_power
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-14T12:00:55.519829+00:00
-- url     : https://prove2.me/theorems/cc796b19-6aa2-4f7a-965b-430148ff6d94
-- title:
--   Low-weight formal jet vanishing implies a local jet ideal power
-- statement:
--   For one center, vanishing of every formal-jet coefficient below the weighted cutoff implies membership in the `n`th power of its local jet ideal, assuming positive weights and exponents, the common scale identity, and the truncation-tail bound. This is the algebraic step relating the full logarithmic formal chart to the truncated polynomial jet coordinates.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Approximation/AdmissibleMatrixGeometry.lean#L41-L44

import Definitions.Def_OAI_PiExponent_AdmissibleFormalInterpolation
import Definitions.Def_OAI_PiExponent_LogarithmicJetIdeals

open OAI.PiExponent
open OAI.PiExponent.AdmissibleFormalInterpolation
open OAI.PiExponent.LogarithmicJetIdeals
open scoped BigOperators

theorem OAI.PiExponent.LogarithmicJetIdeals.low_weight_formal_coefficients_imply_local_power
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
    P ∈ (localJetIdeal c T e) ^ n := by sorry
