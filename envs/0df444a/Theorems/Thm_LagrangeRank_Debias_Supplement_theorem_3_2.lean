-- Prove2me | Theorems.Thm_LagrangeRank_Debias_Supplement_theorem_3_2
-- name    : LagrangeRank.Debias.Supplement.theorem_3_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-24T03:50:44.711557+00:00
-- url     : https://prove2.me/theorems/f091ecb1-6373-4748-a32b-073f67428642
-- title:
--   Theorem 3.2 — both BTL asymptotic normality conclusions
-- statement:
--   Fix a finite dynamic range bound $\kappa\ge1$ and a regularization coefficient $c>0$. There exists a sufficiently large fixed $C_0>0$ such that, for every sequence of BTL problems with centered true log scores $\theta^*$ of dynamic range at most $\kappa$, $n,L\to\infty$, $p\ge C_0\log n/n$ eventually, and
--   $$\frac{n\log n}{\sqrt L}+\frac{\log n}{\sqrt{pL}}\longrightarrow0,$$
--   the Lagrangian debiased regularized MLE satisfies both
--   $$\frac{\sqrt L(\hat\theta_j^d-\theta_j^*)}{\sqrt{[\Theta^*_{11}]_{jj}}}\Rightarrow N(0,1),\qquad
--   \frac{\sqrt L\{\hat\theta_i^d-\hat\theta_j^d-(\theta_i^*-\theta_j^*)\}}{\sqrt{(e_i-e_j)^T\Theta^*_{11}(e_i-e_j)}}\Rightarrow N(0,1).$$
--   Coordinates $i\ne j$ may vary along the sequence. $\Theta^*_{11}$ is the upper-left block of the actual realized-graph bordered inverse at $\theta^*$ in (3.10), hence random. The probability law includes both graph and outcome randomness. No estimation rate, score CLT, inverse approximation or desired conclusion is assumed as an extra premise.
--
--   Differences from the source:
--   - encoding: sample size n and repeated-comparison count L tend to infinity → a separate sequence index t, dimensions n(t), L(t), and finite product probability spaces; reason: the law at each problem size is exactly (2.1); both graph and comparison randomness remain
--   - encoding: inverse in (3.10) on the high-probability invertible graph event → the actual Matrix.inv, with zero on singular inputs; reason: under the stated sufficiently large graph-density constant the exceptional probability vanishes; no population inverse or CLIME estimate is substituted
--   - reading: fixed bounded positive scores in Section 2.1 and the sum-zero constraint in Theorem 3.2 → a fixed bound on every ratio exp(θ_i−θ_j) after centering; reason: Section 2.1 identifies common shifts; absolute uncentered score bounds are not reimposed after centering
-- source:
--   Liu, Fang, Lu, Lagrangian Inference for Ranking Problems, arXiv:2110.00151v1, p. 18, Theorem 3.2

import Mathlib
import Definitions.Def_LagrangeRank_Debias_Supplement_BTL

namespace LagrangeRank.Debias.Supplement

open MeasureTheory ProbabilityTheory Matrix Filter Topology
/-- BTL normality for the actual regularized MLE and realized-graph inverse (3.10). -/
theorem theorem_3_2 (κ c : ℝ) (hκ : 1 ≤ κ) (hc : 0 < c) :
    ∃ C0 : ℝ, 0 < C0 ∧
    ∀ (n L : ℕ → ℕ) (p : ℕ → unitInterval) (θ : (t : ℕ) → Vec (n t))
      (i j : (t : ℕ) → Fin (n t)),
      Regime n L p → Density C0 n p → Rates32 n L p →
      (∀ t, Parameter κ (θ t)) → (∀ t, i t ≠ j t) →
      TendstoInDistribution (fun t s =>
        Real.sqrt (L t) * (thetaD (p t) c s (j t) - θ t (j t)) /
          Real.sqrt (trueBlock s (θ t) (j t) (j t)))
        atTop id (fun t => dataLaw (L t) (p t) (θ t)) (gaussianReal 0 1) ∧
      TendstoInDistribution (fun t s =>
        Real.sqrt (L t) *
          (thetaD (p t) c s (i t) - thetaD (p t) c s (j t) - (θ t (i t) - θ t (j t))) /
          Real.sqrt (pairVar (trueBlock s (θ t)) (i t) (j t)))
        atTop id (fun t => dataLaw (L t) (p t) (θ t)) (gaussianReal 0 1) := by sorry

end LagrangeRank.Debias.Supplement
