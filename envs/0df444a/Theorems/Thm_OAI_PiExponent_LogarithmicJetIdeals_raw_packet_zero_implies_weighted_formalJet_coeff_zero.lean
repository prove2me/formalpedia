-- Prove2me | Theorems.Thm_OAI_PiExponent_LogarithmicJetIdeals_raw_packet_zero_implies_weighted_formalJet_coeff_zero
-- name    : OAI.PiExponent.LogarithmicJetIdeals.raw_packet_zero_implies_weighted_formalJet_coeff_zero
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-15T20:55:05.217751+00:00
-- url     : https://prove2.me/theorems/f8fbadb2-d49f-4f7e-83fa-60de51efaa29
-- title:
--   Raw packet vanishing gives coefficient vanishing below the row cutoff
-- statement:
--   For any center index and exponent vector strictly inside the row-weighted cutoff, vanishing of the raw packet map forces the corresponding formal-jet coefficient to vanish. The strict inequality is required because the packet domain is a strict weighted simplex.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Approximation/AdmissibleMatrixGeometry.lean#L41-L44

import Definitions.Def_OAI_PiExponent_AdmissibleFormalInterpolation
import Definitions.Def_OAI_PiExponent_LogarithmicJetIdeals

open OAI.PiExponent
open OAI.PiExponent.AdmissibleFormalInterpolation
open OAI.PiExponent.LogarithmicJetIdeals

theorem OAI.PiExponent.LogarithmicJetIdeals.raw_packet_zero_implies_weighted_formalJet_coeff_zero
    {m : ℕ} (K : ℕ) (v0 theta : ℝ) (w : Fin m → ℝ) (H : ℝ)
    (r : Fin m → ℂ) (P : MvPolynomial (Fin (m + 1)) ℂ)
    (hpacket : rawPacketMap K v0 theta w H r P = 0)
    (j : Fin K) (a : Fin (m + 1) → ℕ)
    (ha : (∑ i, InterpolationMatrix.rowWeights v0 theta w i * (a i : ℝ)) < H) :
    MvPowerSeries.coeff (InterpolationMatrix.exponentVector a)
      (AdmissibleFormalInterpolation.formalJet
        (fun i => (j.val : ℂ) * r i) P) = 0 := by sorry
