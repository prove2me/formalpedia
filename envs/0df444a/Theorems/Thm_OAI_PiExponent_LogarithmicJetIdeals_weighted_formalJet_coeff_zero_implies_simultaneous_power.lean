-- Prove2me | Theorems.Thm_OAI_PiExponent_LogarithmicJetIdeals_weighted_formalJet_coeff_zero_implies_simultaneous_power
-- name    : OAI.PiExponent.LogarithmicJetIdeals.weighted_formalJet_coeff_zero_implies_simultaneous_power
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-15T20:55:31.295215+00:00
-- url     : https://prove2.me/theorems/4892c660-7b30-4aa3-862f-44348a6b9b61
-- title:
--   Weighted formal-jet vanishing detects simultaneous jet ideal powers
-- statement:
--   If every formal-jet coefficient at every center vanishes below the padded weighted cutoff, then the polynomial belongs to the nth power of the simultaneous jet ideal. Positivity of row weights and exponents, the generator-weight bound, the truncation-tail bound, and injectivity of the center map are retained to support the local ideal-power criterion and its combination across distinct centers.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Approximation/AdmissibleMatrixGeometry.lean#L41-L44

import Definitions.Def_OAI_PiExponent_AdmissibleFormalInterpolation
import Definitions.Def_OAI_PiExponent_LogarithmicJetIdeals

open OAI.PiExponent
open OAI.PiExponent.AdmissibleFormalInterpolation
open OAI.PiExponent.LogarithmicJetIdeals

theorem OAI.PiExponent.LogarithmicJetIdeals.weighted_formalJet_coeff_zero_implies_simultaneous_power
    {m : ℕ} (K : ℕ) (v0 theta : ℝ) (w : Fin m → ℝ) (S : ℝ)
    (r : Fin m → ℂ) (T : Fin m → ℕ) (e : Fin (m + 1) → ℕ)
    (hS : 0 < S)
    (hv : ∀ i, 0 < InterpolationMatrix.rowWeights v0 theta w i)
    (he : ∀ i, 0 < e i)
    (hscale : ∀ i, (e i : ℝ) * InterpolationMatrix.rowWeights v0 theta w i ≤ S)
    (hT : ∀ i : Fin m,
      InterpolationMatrix.rowWeights v0 theta w i.succ ≤ (T i : ℝ) * v0)
    (hc : Function.Injective (fun j : Fin K => fun i : Fin m => (j.val : ℂ) * r i))
    (n : ℕ) (P : MvPolynomial (Fin (m + 1)) ℂ)
    (hcoeff : ∀ (j : Fin K) (a : Fin (m + 1) → ℕ),
      (∑ i, InterpolationMatrix.rowWeights v0 theta w i * (a i : ℝ)) <
        ((n + m : ℕ) : ℝ) * S →
      MvPowerSeries.coeff (InterpolationMatrix.exponentVector a)
        (AdmissibleFormalInterpolation.formalJet
          (fun i => (j.val : ℂ) * r i) P) = 0) :
    P ∈ (simultaneousJetIdeal K r T e) ^ n := by sorry
