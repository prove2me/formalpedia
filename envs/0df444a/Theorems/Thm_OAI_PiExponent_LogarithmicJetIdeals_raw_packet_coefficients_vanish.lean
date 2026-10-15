-- Prove2me | Theorems.Thm_OAI_PiExponent_LogarithmicJetIdeals_raw_packet_coefficients_vanish
-- name    : OAI.PiExponent.LogarithmicJetIdeals.raw_packet_coefficients_vanish
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-14T11:26:43.525839+00:00
-- url     : https://prove2.me/theorems/43787b55-71ca-4d9c-8b5b-16f5cb747526
-- title:
--   Raw packet vanishing gives coefficient vanishing on its row set
-- statement:
--   If the raw packet map vanishes, every coefficient at a center and exponent vector in its strict weighted-simplex row set vanishes.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Approximation/AdmissibleMatrixGeometry.lean#L41-L44

import Definitions.Def_OAI_PiExponent_AdmissibleFormalInterpolation
import Definitions.Def_OAI_PiExponent_LogarithmicJetIdeals

open OAI.PiExponent
open OAI.PiExponent.AdmissibleFormalInterpolation
open OAI.PiExponent.LogarithmicJetIdeals

theorem OAI.PiExponent.LogarithmicJetIdeals.raw_packet_coefficients_vanish
    {m : ℕ} (K : ℕ) (v0 theta : ℝ) (w : Fin m → ℝ) (H : ℝ)
    (r : Fin m → ℂ) (P : MvPolynomial (Fin (m + 1)) ℂ)
    (hpacket : rawPacketMap K v0 theta w H r P = 0) :
    ∀ j : Fin K, ∀ a : Fin (m + 1) → ℕ,
      a ∈ strictWeightedSimplex (InterpolationMatrix.rowWeights v0 theta w) H →
      MvPowerSeries.coeff (InterpolationMatrix.exponentVector a)
        (AdmissibleFormalInterpolation.formalJet
          (fun i => (j.val : ℂ) * r i) P) = 0 := by sorry
