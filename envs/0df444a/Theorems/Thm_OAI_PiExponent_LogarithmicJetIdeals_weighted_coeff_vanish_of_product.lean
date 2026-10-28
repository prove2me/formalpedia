-- Prove2me | Theorems.Thm_OAI_PiExponent_LogarithmicJetIdeals_weighted_coeff_vanish_of_product
-- name    : OAI.PiExponent.LogarithmicJetIdeals.weighted_coeff_vanish_of_product
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-15T20:48:52.49812+00:00
-- url     : https://prove2.me/theorems/81a82f83-3862-4138-8598-cfb7e0113207
-- title:
--   Weighted coefficient vanishing for a product with ideal factors
-- statement:
--   A product of n ideal factors, multiplied by any polynomial Q, has zero coefficients after applying φ below weighted degree nR, provided every ideal element has zero coefficients below weighted degree R.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Approximation/AdmissibleMatrixGeometry.lean#L41-L44

import Definitions.Def_OAI_NumberTheory_PiExponent_Approximation_DeterminantContradiction_CoreData
import Mathlib.RingTheory.MvPowerSeries.Equiv
import Mathlib.RingTheory.Ideal.Operations

open OAI.PiExponent OAI.PiExponent.DeterminantContradiction
open scoped BigOperators

theorem OAI.PiExponent.LogarithmicJetIdeals.weighted_coeff_vanish_of_product
    {m : ℕ} (v : Fin (m + 1) → ℝ) (R : ℝ) (n : ℕ) (hn : 0 < n)
    (hv : ∀ i, 0 < v i)
    (φ : MvPolynomial (Fin (m + 1)) ℂ →+* MvPowerSeries (Fin (m + 1)) ℂ)
    (I : Ideal (MvPolynomial (Fin (m + 1)) ℂ))
    (hcoeff : ∀ (Q : MvPolynomial (Fin (m + 1)) ℂ), Q ∈ I →
      ∀ (a : Fin (m + 1) → ℕ),
        (∑ i, v i * (a i : ℝ)) < R →
        MvPowerSeries.coeff (InterpolationMatrix.exponentVector a) (φ Q) = 0)
    (Q : MvPolynomial (Fin (m + 1)) ℂ)
    (F : Fin n → MvPolynomial (Fin (m + 1)) ℂ)
    (hF : ∀ i, F i ∈ I)
    (a : Fin (m + 1) → ℕ)
    (ha : (∑ i, v i * (a i : ℝ)) < (n : ℝ) * R) :
    MvPowerSeries.coeff (InterpolationMatrix.exponentVector a)
      (φ (Q * ∏ i, F i)) = 0 := by sorry
