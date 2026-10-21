-- Prove2me | Theorems.Thm_HiddenIntSDP_OracleBound_proposition_2
-- name    : HiddenIntSDP.OracleBound.proposition_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T05:05:42.704455+00:00
-- url     : https://prove2.me/theorems/b4a7e2d2-f444-4483-8798-2a818c529d86
-- title:
--   Proposition 2, p. 18 — spectral bound on S₂
-- statement:
--   For each balanced mixture realization and every feasible SDP matrix $Y$,
--   $$S_2\le\frac\gamma\ell\|G\|_{\mathrm{op}}^2,$$
--   where $G$ has the noise vectors as rows, $\ell=n/k$, and $\|G\|_{\mathrm{op}}$ is its spectral norm. Moreover, there is a universal constant $C>0$ such that, if $s^2\ge Ck(d/n+1)$, then with probability at least $1-e^{-n/2}$ the second bound holds simultaneously for every feasible $Y$:
--   $$
--   \frac\gamma\ell\|G\|_{\mathrm{op}}^2\le\frac1{100}\Delta^2\gamma.
--   $$
--
--   This controls the component of the noise Gram matrix orthogonal to the true clustering space.
--
--   **Formalization Note** The matrix norm uses Mathlib's scoped $L^2$ operator norm, not the default matrix norm.
-- source:
--   Fei & Chen, Hidden integrality and semi-random robustness of SDP relaxation for sub-Gaussian mixture model, arXiv:1803.06510v2, p. 18, Proposition 2

import Mathlib
import Definitions.Def_HighDimProb_Deviations_SubgaussianVectorNorm_v2
import Definitions.Def_HiddenIntSDP_OracleBound_Proof

open MeasureTheory ProbabilityTheory
open scoped Matrix.Norms.L2Operator

namespace HiddenIntSDP.OracleBound

/-- Fei–Chen, Proposition 2, p. 18. The matrix norm is the spectral operator norm. -/
theorem proposition_2 :
    (∀ (n k d : ℕ), 4 ≤ n → 2 ≤ k →
      ∀ (sig : Fin n → Fin k), Balanced n k sig →
      ∀ (g : Fin n → EuclideanSpace ℝ (Fin d))
        (Y : Matrix (Fin n) (Fin n) ℝ), SDPFeasible n k Y →
        S2 sig g Y ≤ (gamma sig Y / ell n k) * ‖Gmat g‖ ^ 2) ∧
    ∃ C : ℝ, 0 < C ∧ ∀ (n k d : ℕ), 4 ≤ n → 2 ≤ k →
    ∀ (mu : Fin k → EuclideanSpace ℝ (Fin d)) (sig : Fin n → Fin k), Balanced n k sig →
    ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (g : Fin n → Ω → EuclideanSpace ℝ (Fin d)) (τ : ℝ), 0 < τ →
      (∀ i, Measurable (g i)) → ProbabilityTheory.iIndepFun g P →
      (∀ i, ∫ ω, g i ω ∂P = 0) →
      (∀ i, HighDimProb.Deviations.subgaussianVectorNorm P (g i) ≤ ENNReal.ofReal τ) →
      C * k * (d / n + 1 : ℝ) ≤ (minSep mu / τ) ^ 2 →
        ∃ E : Set Ω, MeasurableSet E ∧
          1 - Real.exp (-(n : ℝ) / 2) ≤ (P E).toReal ∧
          ∀ ω ∈ E, ∀ Y : Matrix (Fin n) (Fin n) ℝ,
            SDPFeasible n k Y →
            (gamma sig Y / ell n k) * ‖Gmat (fun i => g i ω)‖ ^ 2 ≤
              (1 / 100 : ℝ) * minSep mu ^ 2 * gamma sig Y := by sorry

end HiddenIntSDP.OracleBound
