-- Prove2me | Theorems.Thm_HiddenIntSDP_OracleBound_theorem_1
-- name    : HiddenIntSDP.OracleBound.theorem_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T05:04:59.176021+00:00
-- url     : https://prove2.me/theorems/bb512e67-bdb3-4ef1-b3c8-bf4b3db97784
-- title:
--   Theorem 1, p. 10 — SDP error at most twice Oracle error
-- statement:
--   Under Model 1, there exist universal constants $C_s>0$ and $C\ge1$, chosen independently of the dimensions, centers, labels, and noise law, with the following property. If $n\ge4$, $k\ge2$, the clusters are balanced, the independent noises are measurable, zero-mean, and have vector sub-Gaussian norms at most $\tau>0$, and
--   $$
--   s^2\ge C_s\left(\sqrt{\frac{kd}{n}\log n}+\frac{kd}{n}+k\right),
--   \qquad s=\frac\Delta\tau,
--   $$
--   then with probability at least $1-n^{-C}-2e^{-n}$ every optimum $\widehat Y$ of the realized SDP satisfies
--   $$
--   \frac{\|\widehat Y-Y^*\|_1}{\|Y^*\|_1}
--   \le2\max_{\substack{F\in\mathcal F\\\eta(F)\le\eta(F^*)}}
--   \frac{\|F-F^*\|_1}{\|F^*\|_1}.
--   $$
--   The Oracle IP uses the same noise realization, inflated by four in $\bar h_j$. This theorem compares the SDP relaxation with the worst-case Oracle error.
--
--   **Formalization Note** The finite maximum is expressed by existence of a feasible assignment attaining the displayed upper bound. The event is measurable, and its conclusion covers every SDP optimum at every realization in the event.
-- source:
--   Fei & Chen, Hidden integrality and semi-random robustness of SDP relaxation for sub-Gaussian mixture model, arXiv:1803.06510v2, p. 10, Theorem 1, (13)

import Mathlib
import Definitions.Def_HighDimProb_Deviations_SubgaussianVectorNorm_v2
import Definitions.Def_HiddenIntSDP_OracleBound_Model

open MeasureTheory ProbabilityTheory

namespace HiddenIntSDP.OracleBound

/-- Fei–Chen, Theorem 1, p. 10: the relative SDP error is at most twice the
relative worst-case Oracle IP error under the stated SNR condition. -/
theorem theorem_1 :
    ∃ Cs : ℝ, 0 < Cs ∧ ∃ C : ℝ, 1 ≤ C ∧
    ∀ (n k d : ℕ), 4 ≤ n → 2 ≤ k →
    ∀ (mu : Fin k → EuclideanSpace ℝ (Fin d)) (sig : Fin n → Fin k), Balanced n k sig →
    ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (g : Fin n → Ω → EuclideanSpace ℝ (Fin d)) (τ : ℝ), 0 < τ →
      (∀ i, Measurable (g i)) → ProbabilityTheory.iIndepFun g P →
      (∀ i, ∫ ω, g i ω ∂P = 0) →
      (∀ i, HighDimProb.Deviations.subgaussianVectorNorm P (g i) ≤ ENNReal.ofReal τ) →
      Cs * (Real.sqrt ((k * d / n : ℝ) * Real.log n) + k * d / n + k) ≤
        (minSep mu / τ) ^ 2 →
      ∃ E : Set Ω, MeasurableSet E ∧
        1 - (n : ℝ) ^ (-C) - 2 * Real.exp (-(n : ℝ)) ≤ (P E).toReal ∧
        ∀ ω ∈ E, ∀ Y : Matrix (Fin n) (Fin n) ℝ,
          IsSDPOpt n k (distMat (fun i => mu (sig i) + g i ω)) Y →
          ∃ F, IsAssignment F ∧
            eta mu sig (fun i => g i ω) F ≤ eta mu sig (fun i => g i ω) (Fstar sig) ∧
            l1 (Y - Ystar sig) / l1 (Ystar sig) ≤
              2 * (l1 (F - Fstar sig) / l1 (Fstar sig)) := by sorry

end HiddenIntSDP.OracleBound
