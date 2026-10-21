-- Prove2me | Theorems.Thm_HiddenIntSDP_OracleBound_proposition_1
-- name    : HiddenIntSDP.OracleBound.proposition_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T05:05:47.917988+00:00
-- url     : https://prove2.me/theorems/64da7a6c-da1a-43b1-9520-e784cda6a626
-- title:
--   Proposition 1, p. 18 — high-probability bound on S₁
-- statement:
--   Under Model 1, there is a universal constant $C>0$ such that, if
--   $$
--   s^2\ge C\left(\sqrt{\frac{kd}{n}\log n}
--   +\sqrt{\frac{k}{n}}\log n+\frac{kd}{n}\right),
--   \qquad s=\Delta/\tau,
--   $$
--   then, with probability at least $1-n^{-8}$, every optimal solution $Y$ of the realized SDP satisfies
--   $$S_1\le\frac1{100}\Delta^2\gamma,$$
--   where $\gamma=\|Y-Y^*\|_1$. The extra middle term in this proposition's threshold is present in the paper.
--
--   **Formalization Note** The good event is measurable and the bound holds simultaneously for all SDP optima at a realization.
-- source:
--   Fei & Chen, Hidden integrality and semi-random robustness of SDP relaxation for sub-Gaussian mixture model, arXiv:1803.06510v2, p. 18, Proposition 1

import Mathlib
import Definitions.Def_HighDimProb_Deviations_SubgaussianVectorNorm_v2
import Definitions.Def_HiddenIntSDP_OracleBound_Proof

open MeasureTheory ProbabilityTheory

namespace HiddenIntSDP.OracleBound

/-- Fei–Chen, Proposition 1, p. 18. -/
theorem proposition_1 :
    ∃ C : ℝ, 0 < C ∧ ∀ (n k d : ℕ), 4 ≤ n → 2 ≤ k →
    ∀ (mu : Fin k → EuclideanSpace ℝ (Fin d)) (sig : Fin n → Fin k), Balanced n k sig →
    ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (g : Fin n → Ω → EuclideanSpace ℝ (Fin d)) (τ : ℝ), 0 < τ →
      (∀ i, Measurable (g i)) → ProbabilityTheory.iIndepFun g P →
      (∀ i, ∫ ω, g i ω ∂P = 0) →
      (∀ i, HighDimProb.Deviations.subgaussianVectorNorm P (g i) ≤ ENNReal.ofReal τ) →
      C * (Real.sqrt ((k * d / n : ℝ) * Real.log n) +
        Real.sqrt ((k : ℝ) / n) * Real.log n + k * d / n) ≤ (minSep mu / τ) ^ 2 →
      ∃ E : Set Ω, MeasurableSet E ∧
        1 - (n : ℝ) ^ (-(8 : ℝ)) ≤ (P E).toReal ∧
        ∀ ω ∈ E, ∀ Y : Matrix (Fin n) (Fin n) ℝ,
          IsSDPOpt n k (distMat (fun i => mu (sig i) + g i ω)) Y →
          S1 sig (fun i => g i ω) Y ≤
            (1 / 100 : ℝ) * minSep mu ^ 2 * gamma sig Y := by sorry

end HiddenIntSDP.OracleBound
