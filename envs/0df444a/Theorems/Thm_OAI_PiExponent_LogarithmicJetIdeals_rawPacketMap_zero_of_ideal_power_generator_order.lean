-- Prove2me | Theorems.Thm_OAI_PiExponent_LogarithmicJetIdeals_rawPacketMap_zero_of_ideal_power_generator_order
-- name    : OAI.PiExponent.LogarithmicJetIdeals.rawPacketMap_zero_of_ideal_power_generator_order
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-14T11:18:06.472381+00:00
-- url     : https://prove2.me/theorems/dbe107fd-8d10-4824-92a1-ef35aebd88e1
-- title:
--   Generator coefficient order implies vanishing on strict packets
-- statement:
--   If every powered generator at every center has no formal-series coefficients below S, membership in the n-th simultaneous jet-ideal power forces all raw packet coefficients in the strict row simplex below nS to vanish.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Approximation/AdmissibleMatrixGeometry.lean#L41-L44

import Definitions.Def_OAI_NumberTheory_PiExponent_Approximation_DeterminantContradiction_CoreData
import Definitions.Def_OAI_PiExponent_AdmissibleFormalInterpolation
import Definitions.Def_OAI_PiExponent_LogarithmicJetIdeals

open OAI.PiExponent OAI.PiExponent.DeterminantContradiction
open OAI.PiExponent.AdmissibleFormalInterpolation
open OAI.PiExponent.LogarithmicJetIdeals

theorem OAI.PiExponent.LogarithmicJetIdeals.rawPacketMap_zero_of_ideal_power_generator_order
    {m : ℕ} (K : ℕ) (v0 theta : ℝ) (w : Fin m → ℝ)
    (r : Fin m → ℂ) (T : Fin m → ℕ) (e : Fin (m + 1) → ℕ)
    (S : ℝ)
    (hweights : ∀ k, 0 < InterpolationMatrix.rowWeights v0 theta w k)
    (hgen : ∀ (j : Fin K) (i : Fin (m + 1)) (a : Fin (m + 1) → ℕ),
      (∑ k : Fin (m + 1), InterpolationMatrix.rowWeights v0 theta w k * (a k : ℝ)) < S →
      MvPowerSeries.coeff (InterpolationMatrix.exponentVector a)
        (AdmissibleFormalInterpolation.formalJet (fun k => (j.val : ℂ) * r k)
          ((jetCoordinate (fun k => (j.val : ℂ) * r k) T i) ^ e i)) = 0)
    (n : ℕ) (P : MvPolynomial (Fin (m + 1)) ℂ)
    (hP : P ∈ (simultaneousJetIdeal K r T e) ^ n) :
    rawPacketMap K v0 theta w ((n : ℝ) * S) r P = (fun _ => 0) := by sorry
