-- Prove2me | Theorems.Thm_OAI_PiExponent_LogarithmicJetIdeals_weighted_formalJet_coeff_zero_implies_local_power
-- name    : OAI.PiExponent.LogarithmicJetIdeals.weighted_formalJet_coeff_zero_implies_local_power
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-15T21:01:05.205456+00:00
-- url     : https://prove2.me/theorems/53585ad4-03ce-487d-a9a7-5db6109c021f
-- title:
--   Weighted formal-jet vanishing implies a local jet ideal power
-- statement:
--   At one center, vanishing of every formal-jet coefficient below the padded weighted cutoff implies membership in the nth power of that center's local jet ideal. Positivity, scale, and truncation hypotheses are preserved for the local weighted-degree and truncation argument.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Approximation/AdmissibleMatrixGeometry.lean#L41-L44

import Definitions.Def_OAI_PiExponent_AdmissibleFormalInterpolation
import Definitions.Def_OAI_PiExponent_LogarithmicJetIdeals

open OAI.PiExponent
open OAI.PiExponent.AdmissibleFormalInterpolation
open OAI.PiExponent.LogarithmicJetIdeals

theorem OAI.PiExponent.LogarithmicJetIdeals.weighted_formalJet_coeff_zero_implies_local_power
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
    P ∈ localJetIdeal c T e ^ n := by sorry
