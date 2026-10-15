-- Prove2me | Theorems.Thm_OAI_PiExponent_LogarithmicJetIdeals_exists_coeff_factors_of_pow_coeff_ne_zero
-- name    : OAI.PiExponent.LogarithmicJetIdeals.exists_coeff_factors_of_pow_coeff_ne_zero
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-14T13:23:33.120383+00:00
-- url     : https://prove2.me/theorems/46af0451-a971-4ace-9dbd-756152c80b80
-- title:
--   Nonzero power coefficients have nonzero factor coefficients
-- statement:
--   If a coefficient of a natural power of a multivariate formal power series is nonzero, there is a coordinatewise exponent decomposition into one exponent per factor, with each corresponding coefficient of the original series nonzero.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Approximation/AdmissibleMatrixGeometry.lean#L41-L44

import Definitions.Def_OAI_NumberTheory_PiExponent_Approximation_DeterminantContradiction_CoreData
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction
open scoped BigOperators

theorem OAI.PiExponent.LogarithmicJetIdeals.exists_coeff_factors_of_pow_coeff_ne_zero
    {m : ℕ} (F : MvPowerSeries (Fin (m + 1)) ℂ) (n : ℕ)
    (a : Fin (m + 1) → ℕ)
    (hcoeff : MvPowerSeries.coeff (InterpolationMatrix.exponentVector a) (F ^ n) ≠ 0) :
    ∃ b : Fin n → Fin (m + 1) → ℕ,
      (∀ i : Fin n,
        MvPowerSeries.coeff (InterpolationMatrix.exponentVector (b i)) F ≠ 0) ∧
      (∑ i : Fin n, InterpolationMatrix.exponentVector (b i)) =
        InterpolationMatrix.exponentVector a := by sorry
