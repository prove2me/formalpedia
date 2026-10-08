-- Prove2me | Theorems.Thm_OptimalBAI_ChernoffPAC_pairwise_crossing_prob
-- name    : OptimalBAI.ChernoffPAC.pairwise_crossing_prob
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-28T02:03:07.593023+00:00
-- url     : https://prove2.me/theorems/fa198363-5743-4db8-bcbd-0d8542905c22
-- title:
--   Appendix C.1 — P(T_{a,b} < ∞) ≤ δ/(K−1) for μ_a < μ_b
-- statement:
--   Let $\delta \in (0,1)$, let $K$ be the number of arms, and let $\beta(t,\delta) = \log\big(2t(K-1)/\delta\big)$ be the informational threshold. Let $\boldsymbol\mu \in [0,1]^K$ be a Bernoulli bandit model with a unique optimal arm, and let the arms be sampled by an arbitrary (possibly randomized) sampling strategy; $\mathbb P_{\boldsymbol\mu}$ denotes the law of the resulting infinite trajectory. For arms $a, b$ put
--
--   $$T_{a,b} := \inf\{t \in \mathbb N : Z_{a,b}(t) > \beta(t,\delta)\},$$
--
--   where $Z_{a,b}(t)$ is the Bernoulli generalized likelihood ratio statistic. Then for any arms $a, b$ with $\mu_a < \mu_b$,
--
--   $$\mathbb P_{\boldsymbol\mu}(T_{a,b} < \infty) \le \frac{\delta}{K-1}.$$
--
--   In words: the probability that the GLR statistic ever gathers evidence above the threshold for the wrong ordering "$a$ at least as good as $b$" is at most $\delta/(K-1)$, whatever the sampling strategy. Applied to each suboptimal arm $a$ against $b = a^*$ and combined by a union bound over the $K-1$ suboptimal arms, this yields Theorem 10.
--
--   The appendix refers to the threshold of "Proposition 10"; this is a printed slip for Theorem 10.
--
--   **Formalization Note** The event $\{T_{a,b} < \infty\}$ is written as $\{\exists t \ge 1 : Z_{a,b}(t) > \beta(t,\delta)\}$; $t = 0$ is excluded, which changes nothing since $Z_{a,b}(0) = 0$. The probability is the outer measure of this event under the trajectory law, and no measurability is assumed. Since $\mu_a < \mu_b$ forces $a \ne b$, hence $K \ge 2$, the division by $K-1$ is by a positive number. The sampling strategy is any policy of the platform's canonical bandit model (a Markov kernel per round from the observed history to the next arm).
-- source:
--   Garivier, Kaufmann, Optimal Best Arm Identification with Fixed Confidence, arXiv:1602.04589v2, p. 25, Appendix C.1 (displayed claim P_µ(T_{a,b} < ∞) ≤ δ/(K−1)); main-text sketch p. 10

import Mathlib
import Definitions.Def_OptimalBAI_ChernoffPAC_ChernoffRule

open MeasureTheory BanditAlgorithm

namespace OptimalBAI.ChernoffPAC

theorem pairwise_crossing_prob {K : ℕ} (δ : ℝ) (hδ : δ ∈ Set.Ioo (0 : ℝ) 1)
    (π : BanditPolicy K) (μ : Fin K → ℝ) (hμ : ∀ i, μ i ∈ Set.Icc (0 : ℝ) 1)
    (hS : ∃ a₀, ∀ i, i ≠ a₀ → μ i < μ a₀) (a b : Fin K) (hab : μ a < μ b) :
    banditTrajMeasure (bernoulliBandit μ hμ) π
        {ω | ∃ t : ℕ, 1 ≤ t ∧ informationalThreshold K δ t < glrStat a b t ω} ≤
      ENNReal.ofReal (δ / ((K : ℝ) - 1)) := by sorry

end OptimalBAI.ChernoffPAC
