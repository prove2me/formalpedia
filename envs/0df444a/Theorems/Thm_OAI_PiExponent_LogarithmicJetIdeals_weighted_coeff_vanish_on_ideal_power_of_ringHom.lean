-- Prove2me | Theorems.Thm_OAI_PiExponent_LogarithmicJetIdeals_weighted_coeff_vanish_on_ideal_power_of_ringHom
-- name    : OAI.PiExponent.LogarithmicJetIdeals.weighted_coeff_vanish_on_ideal_power_of_ringHom
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-13T18:30:35.265216+00:00
-- url     : https://prove2.me/theorems/955b39c2-70ec-4579-8d11-92c8c26cfafd
-- title:
--   Weighted coefficient vanishing propagates through ideal powers under ring homomorphisms
-- statement:
--   For a ring homomorphism from multivariate polynomials to multivariate power series, if coefficients of every image of an ideal element vanish below weighted degree R, then coefficients of images of members of its positive n-th ideal power vanish below nR, provided all weights are positive.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Approximation/AdmissibleMatrixGeometry.lean#L41-L44

import Definitions.Def_OAI_NumberTheory_PiExponent_Approximation_DeterminantContradiction_CoreData
import Mathlib.RingTheory.MvPowerSeries.Equiv
import Mathlib.RingTheory.Ideal.Operations

open OAI.PiExponent OAI.PiExponent.DeterminantContradiction
open scoped BigOperators

theorem OAI.PiExponent.LogarithmicJetIdeals.weighted_coeff_vanish_on_ideal_power_of_ringHom
    {m : ℕ} (v : Fin (m + 1) → ℝ) (R : ℝ) (n : ℕ) (hn : 0 < n)
    (hv : ∀ i, 0 < v i)
    (I : Ideal (MvPolynomial (Fin (m + 1)) ℂ))
    (φ : MvPolynomial (Fin (m + 1)) ℂ →+* MvPowerSeries (Fin (m + 1)) ℂ)
    (hcoeff : ∀ (Q : MvPolynomial (Fin (m + 1)) ℂ), Q ∈ I →
      ∀ (a : Fin (m + 1) → ℕ),
        (∑ i, v i * (a i : ℝ)) < R →
        MvPowerSeries.coeff (InterpolationMatrix.exponentVector a) (φ Q) = 0)
    (P : MvPolynomial (Fin (m + 1)) ℂ)
    (hP : P ∈ I ^ n)
    (a : Fin (m + 1) → ℕ)
    (ha : (∑ i, v i * (a i : ℝ)) < (n : ℝ) * R) :
    MvPowerSeries.coeff (InterpolationMatrix.exponentVector a) (φ P) = 0 := by sorry
