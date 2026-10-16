-- Prove2me | Theorems.Thm_OAI_PiExponent_LogarithmicJetIdeals_formalJet_coeff_zero_of_simultaneousJetIdeal_pow
-- name    : OAI.PiExponent.LogarithmicJetIdeals.formalJet_coeff_zero_of_simultaneousJetIdeal_pow
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-14T17:07:31.347983+00:00
-- url     : https://prove2.me/theorems/255bbf85-d5a0-45af-91ed-a8a39f09b28d
-- title:
--   Coefficient vanishing propagates through powers of the simultaneous jet ideal
-- statement:
--   For positive row weights, if every powered jet generator at every center has zero formal-series coefficients at weighted degrees strictly below S, then every polynomial in the nth power of the simultaneous jet ideal has zero coefficients at each center at weighted degrees strictly below nS. This is the algebraic propagation step used by the target theorem.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Approximation/AdmissibleMatrixGeometry.lean#L41-L44

import Definitions.Def_OAI_NumberTheory_PiExponent_Approximation_DeterminantContradiction_CoreData
import Definitions.Def_OAI_PiExponent_AdmissibleFormalInterpolation
import Definitions.Def_OAI_PiExponent_LogarithmicJetIdeals

open OAI.PiExponent OAI.PiExponent.DeterminantContradiction
open OAI.PiExponent.AdmissibleFormalInterpolation
open OAI.PiExponent.LogarithmicJetIdeals

theorem OAI.PiExponent.LogarithmicJetIdeals.formalJet_coeff_zero_of_simultaneousJetIdeal_pow
    {m : ℕ} (K : ℕ) (v0 theta : ℝ) (w : Fin m → ℝ)
    (r : Fin m → ℂ) (T : Fin m → ℕ) (e : Fin (m + 1) → ℕ)
    (S : ℝ)
    (hweights : ∀ k, 0 < InterpolationMatrix.rowWeights v0 theta w k)
    (hgen : ∀ (j : Fin K) (i : Fin (m + 1)) (a : Fin (m + 1) → ℕ),
      (∑ k : Fin (m + 1), InterpolationMatrix.rowWeights v0 theta w k * (a k : ℝ)) < S →
      MvPowerSeries.coeff (InterpolationMatrix.exponentVector a)
        (AdmissibleFormalInterpolation.formalJet (fun k => (j.val : ℂ) * r k)
          ((jetCoordinate (fun k => (j.val : ℂ) * r k) T i) ^ e i)) = 0)
    (n : ℕ) (P : MvPolynomial (Fin (m + 1)) ℂ)
    (hP : P ∈ (simultaneousJetIdeal K r T e) ^ n)
    (j : Fin K) (a : Fin (m + 1) → ℕ)
    (ha : (∑ k : Fin (m + 1), InterpolationMatrix.rowWeights v0 theta w k * (a k : ℝ)) < (n : ℝ) * S) :
    MvPowerSeries.coeff (InterpolationMatrix.exponentVector a)
      (AdmissibleFormalInterpolation.formalJet (fun k => (j.val : ℂ) * r k) P) = 0 := by sorry
