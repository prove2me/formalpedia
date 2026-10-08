-- Prove2me | Theorems.Thm_OptimalBAI_ChernoffPAC_chernoff_informational_threshold_pac
-- name    : OptimalBAI.ChernoffPAC.chernoff_informational_threshold_pac
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-28T02:03:39.596687+00:00
-- url     : https://prove2.me/theorems/8eeff8ca-5eea-41af-b82d-76d36c183681
-- title:
--   Theorem 10 — Chernoff's stopping rule with β(t,δ) = log(2t(K−1)/δ) is δ-PAC on Bernoulli bandits
-- statement:
--   Let $K \ge 1$ be the number of arms and $\delta \in (0,1)$. Consider Bernoulli bandits: each model $\boldsymbol\mu = (\mu_1,\dots,\mu_K) \in [0,1]^K$ with a unique optimal arm $a^*(\boldsymbol\mu)$ (the class $\mathcal S$). Arms are sampled by an arbitrary, possibly randomized, sampling strategy. The learner stops according to Chernoff's stopping rule (8),
--
--   $$\tau_\delta = \inf\{t \ge 1 : \exists a \in \mathcal A,\ \forall b \in \mathcal A\setminus\{a\},\ Z_{a,b}(t) > \beta(t,\delta)\},$$
--
--   where $Z_{a,b}(t)$ is the Bernoulli generalized likelihood ratio statistic, with the threshold
--
--   $$\beta(t,\delta) = \log\left(\frac{2t(K-1)}{\delta}\right),$$
--
--   and recommends the empirically best arm $\hat a_{\tau_\delta} \in \operatorname{argmax}_{a} \hat\mu_a(\tau_\delta)$, where $\hat\mu_a(t)$ is the empirical mean of arm $a$ after $t$ rounds. Then for every $\boldsymbol\mu \in \mathcal S$,
--
--   $$\mathbb P_{\boldsymbol\mu}\big(\tau_\delta < \infty,\ \hat a_{\tau_\delta} \ne a^*\big) \le \delta .$$
--
--   This is the error half of the $\delta$-PAC property, and it holds whatever the sampling rule, so Chernoff's stopping rule can be combined with any sampling strategy (in particular the Track-and-Stop tracking rules) without compromising the confidence guarantee.
--
--   **Formalization Note** The conclusion is `IsSoundBAI` of the platform's `BanditTrajectory` definition: for every model of the class, the outer measure of $\{\tau_\delta < \infty,\ \Delta_{\hat a} > 0\}$ is at most $\delta$, where $\Delta_{\hat a}$ is the gap of the recommended arm. With a unique optimal arm, $\Delta_{\hat a} > 0$ iff $\hat a \ne a^*$, so this is exactly the paper's event. The sampling strategy is any `BanditPolicy`. The decision rule is not fixed: the theorem holds for every recommendation $\psi$ that, whenever $\tau_\delta = n$ is finite, maximizes the empirical mean after $n$ rounds, so every tie-breaking is covered. The stopping rule is taken over $t \ge 1$ (round $0$ has no observations). Nothing requires $K \ge 2$: for $K = 1$ there is no suboptimal arm and the statement holds trivially. Means $0$ and $1$ are allowed (see the definition). The paper's other half of $\delta$-PAC, $\mathbb P_{\boldsymbol\mu}(\tau_\delta < \infty) = 1$, is not part of Theorem 10 and is not claimed.
-- source:
--   Garivier, Kaufmann, Optimal Best Arm Identification with Fixed Confidence, arXiv:1602.04589v2, p. 10, Theorem 10 (decision rule p. 7; stopping rule eq. (8), p. 8; proof Appendix C.1, pp. 25–26)

import Mathlib
import Definitions.Def_OptimalBAI_ChernoffPAC_ChernoffRule

open MeasureTheory BanditAlgorithm

namespace OptimalBAI.ChernoffPAC

theorem chernoff_informational_threshold_pac {K : ℕ} [NeZero K] (δ : ℝ)
    (hδ : δ ∈ Set.Ioo (0 : ℝ) 1) (π : BanditPolicy K)
    (ψ : (ℕ → Fin K × ℝ) → Fin K)
    (hψ : ∀ (ω : ℕ → Fin K × ℝ) (n : ℕ),
      chernoffStop (informationalThreshold K δ) ω = n →
        ∀ b : Fin K, trajEmpiricalMean b n ω ≤ trajEmpiricalMean (ψ ω) n ω) :
    IsSoundBAI δ π (chernoffStop (informationalThreshold K δ)) ψ (bernoulliClass K) := by sorry

end OptimalBAI.ChernoffPAC
