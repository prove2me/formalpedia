-- Prove2me | Theorems.Thm_OAI_PiExponent_LogarithmicJetIdeals_formalJet_coeff_pow_zero_of_support_bound
-- name    : OAI.PiExponent.LogarithmicJetIdeals.formalJet_coeff_pow_zero_of_support_bound
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-14T12:37:43.85352+00:00
-- url     : https://prove2.me/theorems/cac9cf07-9e38-4dc2-9979-757d9d9cd7cb
-- title:
--   Positive powers preserve weighted coefficient support bounds
-- statement:
--   If a multivariate formal power series has no coefficients of weighted degree strictly below B, its positive nth power has no coefficients of weighted degree strictly below nB. The weights and B may be arbitrary real numbers.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Approximation/AdmissibleMatrixGeometry.lean#L41-L44

import Definitions.Def_OAI_NumberTheory_PiExponent_Approximation_DeterminantContradiction_CoreData
import Definitions.Def_OAI_PiExponent_AdmissibleFormalInterpolation
import Definitions.Def_OAI_PiExponent_LogarithmicJetIdeals

open OAI.PiExponent OAI.PiExponent.DeterminantContradiction
open OAI.PiExponent.AdmissibleFormalInterpolation
open OAI.PiExponent.LogarithmicJetIdeals
open scoped BigOperators

theorem OAI.PiExponent.LogarithmicJetIdeals.formalJet_coeff_pow_zero_of_support_bound
    {m : ℕ} (wt : Fin (m + 1) → ℝ)
    (F : MvPowerSeries (Fin (m + 1)) ℂ) (B : ℝ) (n : ℕ)
    (hF : ∀ b : Fin (m + 1) → ℕ,
      (∑ k : Fin (m + 1), wt k * (b k : ℝ)) < B →
        MvPowerSeries.coeff (InterpolationMatrix.exponentVector b) F = 0)
    (hn : 0 < n) (a : Fin (m + 1) → ℕ)
    (ha : (∑ k : Fin (m + 1), wt k * (a k : ℝ)) < (n : ℝ) * B) :
    MvPowerSeries.coeff (InterpolationMatrix.exponentVector a) (F ^ n) = 0 := by sorry
