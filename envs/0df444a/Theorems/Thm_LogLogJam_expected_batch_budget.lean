-- Prove2me | Theorems.Thm_LogLogJam_expected_batch_budget
-- name    : LogLogJam.expected_batch_budget
-- status  : Proved
-- author  : @Senrui Chen
-- created : 2026-11-26T09:25:06.081973+00:00
-- url     : https://prove2.me/theorems/90b2e50b-d025-4592-8f07-0b3305fbeaac
-- title:
--   Expected batch sizes sum to at most the adaptive copy budget
-- statement:
--   Fix $\lambda>1$. In a protocol with $T\ge0$ Gaussian measurement rounds, the batch size $k_t$ at round $t$ is selected by the seed kernel conditional on the observed length-$t$ history. If every real angle gives probability zero to terminal histories with more than $S$ copies in total, then $\sum_{t<T}\mathbb E_{\theta,H_t}[\mathbb E(k_t\mid H_t)]\le S$, where $\theta$ is uniform on $[0,\pi)$ and $H_t$ has the iterated Gaussian observation law at that angle. The stated expectations use the round's seed law and the history through the preceding round.
-- source:
--   Auxiliary consequence formulated for the rotated squeezed states and adaptive observation model in Chen, Gong, Ye and Zhang, The loglog jam in Gaussian state tomography, arXiv:2607.12983v1. Section 5.2, Eq. (38) and Section 5.4, Eq. (53), give the transcript and its one-step extension. Section 6.2.2 defines the running copy count and budget. This expectation inequality is an auxiliary cost-accounting consequence. https://arxiv.org/html/2607.12983v1#S5.E38

import Definitions.Def_LogLogJam_GaussProtocol

open MeasureTheory
open scoped ENNReal

namespace LogLogJam

theorem expected_batch_budget (lam : ℝ) (hlam : 1 < lam) {T : ℕ}
    (P : GaussProtocol T) (S : ℕ) (hS : CopiesLe lam P S) :
    ∑ t ∈ Finset.range T, ENNReal.ofReal (1 / Real.pi) * ∫⁻ θ in Set.Ico 0 Real.pi,
      histInt lam θ P t (fun H => ∫⁻ s, (s.1 : ℝ≥0∞) ∂(P.seed t H)) ≤ S := by sorry

end LogLogJam
