-- Prove2me | Theorems.Thm_OAI_PiExponent_LogarithmicJetIdeals_zero_padded_raw_packet_local_power
-- name    : OAI.PiExponent.LogarithmicJetIdeals.zero_padded_raw_packet_local_power
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-13T22:56:41.237974+00:00
-- url     : https://prove2.me/theorems/99961622-d624-43d2-8506-12e25c4b532b
-- title:
--   Padded packet vanishing implies local jet ideal powers
-- statement:
--   Vanishing of the raw packet below the padded weighted cutoff implies membership in the nth power of the local jet ideal at every center. This is the local coefficient-to-ideal-power step and retains the target’s positivity, common-scale, and truncation-tail hypotheses.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Approximation/AdmissibleMatrixGeometry.lean#L41-L44

import Definitions.Def_OAI_PiExponent_AdmissibleFormalInterpolation
import Definitions.Def_OAI_PiExponent_LogarithmicJetIdeals

open OAI.PiExponent
open OAI.PiExponent.AdmissibleFormalInterpolation
open OAI.PiExponent.LogarithmicJetIdeals

theorem OAI.PiExponent.LogarithmicJetIdeals.zero_padded_raw_packet_local_power
    {m : ℕ} (K : ℕ) (v0 theta : ℝ) (w : Fin m → ℝ) (R : ℝ)
    (r : Fin m → ℂ) (T : Fin m → ℕ) (e : Fin (m + 1) → ℕ)
    (hR : 0 < R)
    (hv : ∀ i, 0 < InterpolationMatrix.rowWeights v0 theta w i)
    (he : ∀ i, 0 < e i)
    (hscale : ∀ i, R = (e i : ℝ) * InterpolationMatrix.rowWeights v0 theta w i)
    (hT : ∀ i : Fin m,
      InterpolationMatrix.rowWeights v0 theta w i.succ ≤ (T i : ℝ) * v0)
    (n : ℕ) (P : MvPolynomial (Fin (m + 1)) ℂ)
    (hpacket : rawPacketMap K v0 theta w (((n + m : ℕ) : ℝ) * R) r P = 0) :
    ∀ j : Fin K,
      P ∈ (localJetIdeal (fun i => (j.val : ℂ) * r i) T e) ^ n := by sorry
