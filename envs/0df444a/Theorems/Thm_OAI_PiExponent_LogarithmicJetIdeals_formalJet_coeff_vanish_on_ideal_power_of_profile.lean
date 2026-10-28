-- Prove2me | Theorems.Thm_OAI_PiExponent_LogarithmicJetIdeals_formalJet_coeff_vanish_on_ideal_power_of_profile
-- name    : OAI.PiExponent.LogarithmicJetIdeals.formalJet_coeff_vanish_on_ideal_power_of_profile
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-13T18:21:36.904364+00:00
-- url     : https://prove2.me/theorems/45fff3f1-8f55-4996-ba4b-ed2f4217da68
-- title:
--   Coefficient support vanishing propagates through ideal powers
-- statement:
--   For positive n, the coefficient profile for members of I propagates to every member of I^n: at each center j, coefficients of weighted degree strictly below nR vanish. This holds for every real R; positive row weights ensure exponent degrees are nonnegative, including when R or nR is nonpositive.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Approximation/AdmissibleMatrixGeometry.lean#L41-L44

import Definitions.Def_OAI_PiExponent_ApproximationDefinitions
import Definitions.Def_OAI_NumberTheory_PiExponent_Approximation_DeterminantContradiction_CoreData
import Definitions.Def_OAI_PiExponent_AdmissibleFormalInterpolation
import Definitions.Def_OAI_PiExponent_LogarithmicJetIdeals

open OAI.PiExponent OAI.PiExponent.DeterminantContradiction
open OAI.PiExponent.AdmissibleFormalInterpolation
open OAI.PiExponent.LogarithmicJetIdeals
open scoped BigOperators

theorem OAI.PiExponent.LogarithmicJetIdeals.formalJet_coeff_vanish_on_ideal_power_of_profile
    {m : ℕ} (K : ℕ) (v0 theta : ℝ) (w : Fin m → ℝ) (r : Fin m → ℂ)
    (R : ℝ) (n : ℕ) (hn : 0 < n)
    (hv : ∀ i, 0 < InterpolationMatrix.rowWeights v0 theta w i)
    (I : Ideal (MvPolynomial (Fin (m + 1)) ℂ))
    (hcoeff : ∀ (Q : MvPolynomial (Fin (m + 1)) ℂ), Q ∈ I →
      ∀ (j : Fin K) (a : Fin (m + 1) → ℕ),
        (∑ i, InterpolationMatrix.rowWeights v0 theta w i * (a i : ℝ)) < R →
        MvPowerSeries.coeff (InterpolationMatrix.exponentVector a)
          (AdmissibleFormalInterpolation.formalJet
            (fun i => (j.val : ℂ) * r i) Q) = 0)
    (P : MvPolynomial (Fin (m + 1)) ℂ)
    (hP : P ∈ I ^ n)
    (j : Fin K) (a : Fin (m + 1) → ℕ)
    (ha : (∑ i, InterpolationMatrix.rowWeights v0 theta w i * (a i : ℝ)) <
      (n : ℝ) * R) :
    MvPowerSeries.coeff (InterpolationMatrix.exponentVector a)
      (AdmissibleFormalInterpolation.formalJet
        (fun i => (j.val : ℂ) * r i) P) = 0 := by sorry
