-- Prove2me | Theorems.Thm_OAI_PiExponent_LogarithmicJetIdeals_formalJet_jetCoordinate_coeff_zero_of_weight_lt
-- name    : OAI.PiExponent.LogarithmicJetIdeals.formalJet_jetCoordinate_coeff_zero_of_weight_lt
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-14T12:38:11.086195+00:00
-- url     : https://prove2.me/theorems/bd1dbdba-2dab-4732-bd5a-ab3fa5143b5d
-- title:
--   Formalized jet coordinates have no coefficients below their row weight
-- statement:
--   Under positive row weights and the truncation bounds, every formalized jet coordinate has zero coefficients at weighted degrees strictly below its own row weight, for any center. Successor coordinates retain their variable term and a logarithmic tail beginning at the truncation cutoff.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Approximation/AdmissibleMatrixGeometry.lean#L41-L44

import Definitions.Def_OAI_NumberTheory_PiExponent_Approximation_DeterminantContradiction_CoreData
import Definitions.Def_OAI_PiExponent_AdmissibleFormalInterpolation
import Definitions.Def_OAI_PiExponent_LogarithmicJetIdeals

open OAI.PiExponent OAI.PiExponent.DeterminantContradiction
open OAI.PiExponent.AdmissibleFormalInterpolation
open OAI.PiExponent.LogarithmicJetIdeals
open scoped BigOperators

theorem OAI.PiExponent.LogarithmicJetIdeals.formalJet_jetCoordinate_coeff_zero_of_weight_lt
    {m : ℕ} (v0 theta : ℝ) (w : Fin m → ℝ)
    (c : Fin m → ℂ) (T : Fin m → ℕ)
    (hweights : ∀ k, 0 < InterpolationMatrix.rowWeights v0 theta w k)
    (hT : ∀ k, InterpolationMatrix.rowWeights v0 theta w k.succ ≤ (T k : ℝ) * v0)
    (i : Fin (m + 1)) (a : Fin (m + 1) → ℕ)
    (ha : (∑ k : Fin (m + 1), InterpolationMatrix.rowWeights v0 theta w k * (a k : ℝ)) <
      InterpolationMatrix.rowWeights v0 theta w i) :
    MvPowerSeries.coeff (InterpolationMatrix.exponentVector a)
      (AdmissibleFormalInterpolation.formalJet c (jetCoordinate c T i)) = 0 := by sorry
