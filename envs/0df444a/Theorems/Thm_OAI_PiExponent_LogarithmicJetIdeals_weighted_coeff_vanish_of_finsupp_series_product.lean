-- Prove2me | Theorems.Thm_OAI_PiExponent_LogarithmicJetIdeals_weighted_coeff_vanish_of_finsupp_series_product
-- name    : OAI.PiExponent.LogarithmicJetIdeals.weighted_coeff_vanish_of_finsupp_series_product
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-15T20:59:44.583401+00:00
-- url     : https://prove2.me/theorems/1dd71ff3-c24a-4bd1-95ba-d09d72e31334
-- title:
--   Weighted coefficient vanishing for finite products with individual thresholds
-- statement:
--   For positive coordinate weights, let a finite family of multivariate power series have individual coefficient cutoffs T i, and let q have zero coefficients below weighted degree zero. Then q times the product of the family has zero coefficients below the sum of the individual cutoffs.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Approximation/AdmissibleMatrixGeometry.lean#L41-L44

import Definitions.Def_OAI_NumberTheory_PiExponent_Approximation_DeterminantContradiction_CoreData
import Mathlib.RingTheory.MvPowerSeries.Equiv
import Mathlib.RingTheory.Ideal.Operations

open OAI.PiExponent OAI.PiExponent.DeterminantContradiction
open scoped BigOperators

theorem OAI.PiExponent.LogarithmicJetIdeals.weighted_coeff_vanish_of_finsupp_series_product
    {m : ℕ} (v : Fin (m + 1) → ℝ) (n : ℕ) (T : Fin n → ℝ)
    (hv : ∀ j, 0 < v j)
    (A : Fin n → MvPowerSeries (Fin (m + 1)) ℂ)
    (q : MvPowerSeries (Fin (m + 1)) ℂ)
    (hA : ∀ i (d : Fin (m + 1) →₀ ℕ),
      (∑ j, v j * (d j : ℝ)) < T i →
      MvPowerSeries.coeff d (A i) = 0)
    (hq : ∀ (d : Fin (m + 1) →₀ ℕ),
      (∑ j, v j * (d j : ℝ)) < 0 →
      MvPowerSeries.coeff d q = 0)
    (d : Fin (m + 1) →₀ ℕ)
    (hd : (∑ j, v j * (d j : ℝ)) < ∑ i, T i) :
    MvPowerSeries.coeff d (q * ∏ i, A i) = 0 := by sorry
