-- Prove2me | Theorems.Thm_OAI_PiExponent_LogarithmicJetIdeals_weighted_coeff_vanish_of_series_product
-- name    : OAI.PiExponent.LogarithmicJetIdeals.weighted_coeff_vanish_of_series_product
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-15T20:53:16.516315+00:00
-- url     : https://prove2.me/theorems/43d8a04e-767e-4022-b69f-30c1c3c81d9d
-- title:
--   Weighted coefficient vanishing for a finite product of multivariate power series
-- statement:
--   For n positive, if each of n multivariate power series has zero coefficients below weighted degree R, then multiplying them together and multiplying by any additional series yields zero coefficients below weighted degree nR, for positive coordinate weights.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Approximation/AdmissibleMatrixGeometry.lean#L41-L44

import Definitions.Def_OAI_NumberTheory_PiExponent_Approximation_DeterminantContradiction_CoreData
import Mathlib.RingTheory.MvPowerSeries.Equiv
import Mathlib.RingTheory.Ideal.Operations

open OAI.PiExponent OAI.PiExponent.DeterminantContradiction
open scoped BigOperators

theorem OAI.PiExponent.LogarithmicJetIdeals.weighted_coeff_vanish_of_series_product
    {m : ℕ} (v : Fin (m + 1) → ℝ) (R : ℝ) (n : ℕ) (hn : 0 < n)
    (hv : ∀ i, 0 < v i)
    (A : Fin n → MvPowerSeries (Fin (m + 1)) ℂ)
    (q : MvPowerSeries (Fin (m + 1)) ℂ)
    (hA : ∀ i (a : Fin (m + 1) → ℕ),
      (∑ j, v j * (a j : ℝ)) < R →
      MvPowerSeries.coeff (InterpolationMatrix.exponentVector a) (A i) = 0)
    (a : Fin (m + 1) → ℕ)
    (ha : (∑ j, v j * (a j : ℝ)) < (n : ℝ) * R) :
    MvPowerSeries.coeff (InterpolationMatrix.exponentVector a)
      (q * ∏ i, A i) = 0 := by sorry
