-- Prove2me | Theorems.Thm_OAI_PiExponent_LogarithmicJetIdeals_formalJet_jetCoordinate_pow_coeff_zero_of_weight_lt
-- name    : OAI.PiExponent.LogarithmicJetIdeals.formalJet_jetCoordinate_pow_coeff_zero_of_weight_lt
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-14T11:17:39.971793+00:00
-- url     : https://prove2.me/theorems/50cc4330-0cfa-4a8f-a51d-d9e4975b8f5a
-- title:
--   Powered logarithmic jet generators have no coefficients below their weight
-- statement:
--   For every center and powered jet coordinate, the formal series has zero coefficients at exponents whose row-weighted degree is strictly below the common generator weight S. The successor-coordinate tail begins at degree T, while the first coordinate maps to X 0.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Approximation/AdmissibleMatrixGeometry.lean#L41-L44

import Definitions.Def_OAI_NumberTheory_PiExponent_Approximation_DeterminantContradiction_CoreData
import Definitions.Def_OAI_PiExponent_AdmissibleFormalInterpolation
import Definitions.Def_OAI_PiExponent_LogarithmicJetIdeals

open OAI.PiExponent OAI.PiExponent.DeterminantContradiction
open OAI.PiExponent.AdmissibleFormalInterpolation
open OAI.PiExponent.LogarithmicJetIdeals

theorem OAI.PiExponent.LogarithmicJetIdeals.formalJet_jetCoordinate_pow_coeff_zero_of_weight_lt
    {m : ℕ} (K : ℕ) (v0 theta : ℝ) (w : Fin m → ℝ)
    (r : Fin m → ℂ) (T : Fin m → ℕ) (e : Fin (m + 1) → ℕ)
    (S : ℝ)
    (hweights : ∀ k, 0 < InterpolationMatrix.rowWeights v0 theta w k)
    (he : ∀ k, 0 < e k)
    (hcommon : ∀ k, S = (e k : ℝ) * InterpolationMatrix.rowWeights v0 theta w k)
    (hT : ∀ k, InterpolationMatrix.rowWeights v0 theta w k.succ ≤ (T k : ℝ) * v0)
    (j : Fin K) (i : Fin (m + 1)) (a : Fin (m + 1) → ℕ)
    (ha : (∑ k : Fin (m + 1), InterpolationMatrix.rowWeights v0 theta w k * (a k : ℝ)) < S) :
    MvPowerSeries.coeff (InterpolationMatrix.exponentVector a)
      (AdmissibleFormalInterpolation.formalJet (fun k => (j.val : ℂ) * r k)
        ((jetCoordinate (fun k => (j.val : ℂ) * r k) T i) ^ e i)) = 0 := by sorry
