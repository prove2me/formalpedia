-- Prove2me | Theorems.Thm_LogLogJam_posterior_one_step_law
-- name    : LogLogJam.posterior_one_step_law
-- status  : Proved
-- author  : @Senrui Chen
-- created : 2026-11-26T09:35:52.931514+00:00
-- url     : https://prove2.me/theorems/c9062490-c1eb-497f-9cb4-037ac17440e0
-- title:
--   One-round posterior tower law for randomized Gaussian protocols
-- statement:
--   For any real squeezing parameter greater than one, any Gaussian protocol, any round before its terminal time, and any extended nonnegative test measurable on physical histories of the next length, its phase-averaged expectation at that length equals the phase-averaged expectation at the preceding length of its posterior-predictive integral. The latter integral first averages the readout with its posterior predictive density at the selected seed, and then averages over the protocol’s seed kernel at the preceding history.
-- source:
--   Chen, Gong, Ye and Zhang, arXiv:2607.12983, §6.2.2, conditioning on the previous transcript in the proof preceding Eq. (18). https://arxiv.org/abs/2607.12983

import Definitions.Def_LogLogJam_GaussProtocol
open MeasureTheory
open scoped ENNReal

namespace LogLogJam
theorem posterior_one_step_law {T : ℕ} (P : GaussProtocol T) (lam : ℝ) (hlam : 1 < lam)
    (t : ℕ) (ht : t+1 ≤ T) (F : Hist (t+1) → ℝ≥0∞)
    (hF : Measurable (fun H : {H : Hist (t+1) // ∀ i, IsCov (H i).1 (Matrix.of (H i).2.1)} =>
      F H.val)) :
    ENNReal.ofReal (1 / Real.pi) * (∫⁻ θ in Set.Ico 0 Real.pi, histInt lam θ P (t+1) F) =
      ENNReal.ofReal (1 / Real.pi) * (∫⁻ θ in Set.Ico 0 Real.pi, histInt lam θ P t
        (fun H => ∫⁻ s, nextCondExp lam H s.1 s.2 F ∂(P.seed t H))) := by sorry
end LogLogJam
