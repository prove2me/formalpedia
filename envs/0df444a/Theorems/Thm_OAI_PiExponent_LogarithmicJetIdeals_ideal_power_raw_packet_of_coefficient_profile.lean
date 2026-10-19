-- Prove2me | Theorems.Thm_OAI_PiExponent_LogarithmicJetIdeals_ideal_power_raw_packet_of_coefficient_profile
-- name    : OAI.PiExponent.LogarithmicJetIdeals.ideal_power_raw_packet_of_coefficient_profile
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-13T18:11:42.47688+00:00
-- url     : https://prove2.me/theorems/4dbf9569-e759-4fef-9396-73f18d1b4e22
-- title:
--   Coefficient profiles propagate through ideal powers
-- statement:
--   If every element of an ideal has zero formal-jet coefficients below weighted degree R, every element of its nth power has zero raw packet at height nR. This packages the product coefficient allocation and ideal-power expansion step.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Approximation/AdmissibleMatrixGeometry.lean#L41-L44

import Definitions.Def_OAI_PiExponent_ApproximationDefinitions
import Definitions.Def_OAI_NumberTheory_PiExponent_Approximation_DeterminantContradiction_CoreData
import Definitions.Def_OAI_PiExponent_AdmissibleFormalInterpolation
import Definitions.Def_OAI_PiExponent_LogarithmicJetIdeals

open OAI.PiExponent OAI.PiExponent.DeterminantContradiction
open OAI.PiExponent.AdmissibleFormalInterpolation
open OAI.PiExponent.LogarithmicJetIdeals

theorem OAI.PiExponent.LogarithmicJetIdeals.ideal_power_raw_packet_of_coefficient_profile
    {m : ℕ} (K : ℕ) (v0 theta : ℝ) (w : Fin m → ℝ) (r : Fin m → ℂ)
    (R : ℝ) (n : ℕ)
    (hv : ∀ i, 0 < InterpolationMatrix.rowWeights v0 theta w i)
    (I : Ideal (MvPolynomial (Fin (m + 1)) ℂ))
    (hcoeff : ∀ (Q : MvPolynomial (Fin (m + 1)) ℂ), Q ∈ I →
      ∀ (j : Fin K) (a : Fin (m + 1) → ℕ),
        (∑ i, InterpolationMatrix.rowWeights v0 theta w i * (a i : ℝ)) < R →
        MvPowerSeries.coeff (InterpolationMatrix.exponentVector a)
          (AdmissibleFormalInterpolation.formalJet
            (fun i => (j.val : ℂ) * r i) Q) = 0)
    (P : MvPolynomial (Fin (m + 1)) ℂ)
    (hP : P ∈ I ^ n) :
    rawPacketMap K v0 theta w ((n : ℝ) * R) r P = 0 := by sorry
