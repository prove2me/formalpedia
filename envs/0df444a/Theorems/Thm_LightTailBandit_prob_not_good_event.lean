-- Prove2me | Theorems.Thm_LightTailBandit_prob_not_good_event
-- name    : LightTailBandit.prob_not_good_event
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T09:25:52.433027+00:00
-- url     : https://prove2.me/theorems/3b266558-1b89-4750-8c0f-bc56935016aa
-- title:
--   Proof of Theorem 5, App. p.17 — $P(\bar G)\le2KT^{1-\eta_2/2}$
-- statement:
--   Throughout, $K\ge2$ arms and a horizon $T$ with $T\ge3$ and $T\ge K$ are fixed, $\sigma>0$, rounds are $t=1,\dots,T$, and the reward of round $t$ is $r_{t,a_t}=\theta_{a_t}+\epsilon_{t,a_t}$, where the noise $\epsilon_{t,k}$ of round $t$ and arm $k$ is independent of everything observed before round $t$ and is $\sigma$-sub-Gaussian: $\mathbb E[e^{\lambda\epsilon_{t,k}}]\le e^{\lambda^2\sigma^2/2}$ for all real $\lambda$. The action $a_t$ may depend only on the past (and on independent internal randomization). $n_k$ is the number of pulls of arm $k$ in the $T$ rounds, $\theta_*=\max_k\theta_k$, $\Delta_k=\theta_*-\theta_k\le1$, and the bonus is $\mathrm{rad}(n)=\sigma\sqrt{\ln T/n}\,\max\{\sqrt{\eta_1T/(nK)},\sqrt{\eta_2}\}$ (6).
--
--   For every admissible policy and tuning parameters $\eta_1,\eta_2\ge0$, the good event $G$ (for every arm $k$ and $1\le n\le\min(T,n_k)$, $|\Sigma_k(n)|/n\le\mathrm{rad}(n)$) satisfies
--   $$
--   P(\bar G)\le2KT^{1-\eta_2/2}.
--   $$
--
--   With $\eta_2\ge4$ this gives $T\cdot P(\bar G)\le2K$, the additive $2K$ in the expected-regret bound of Theorem 5.
--
--   **Formalization Note** The power is the real power `Real.rpow`.
--
--   Differences from the source:
--   - reading: ϵ_{t,k} is σ-subGaussian, glossed on p.8 as max{P(ϵ_{t,k} ≥ x), P(ϵ_{t,k} ≤ −x)} ≤ exp(−x²/(2σ²)) → E[exp(λ ε t k)] ≤ exp(λ²σ²/2) for every real λ (HasSubgaussianMGF with parameter σ²); reason: Lemma 1 and every 'concentration of subGaussian variables' step of the proof need the moment-generating-function bound, which the tail display does not imply (Lemma 1 fails under the display alone: two-point noise ±σ√(2 ln 2), T = 36, P(N ≥ 18a) = 135142796/2³⁶ > 2⁻⁹); the MGF condition is the standard meaning of σ-subGaussian and covers the Gaussian and bounded noises named on p.9
--   - generalization: noise ϵ_{t,k} sampled independently, zero mean, for each round and arm; the policy maps the history H_t (and its own randomization) to a_t → a noise table ε t k and a filtration ℱ with ε t k ℱ(t+1)-measurable and independent of ℱ t, and a t ℱ t-measurable; no independence across arms within a round is assumed; reason: the paper's model is the special case ℱ t = σ(noises of rounds before t, the policy's internal randomness up to t); only the independence of each round's noise from the past is used
--   - reading: P(Ḡ) ≤ … ≤ 2KT^{1−η/2}, with η undefined in Theorem 5 and the middle term copied from the proof of Theorem 4 → P(Ḡ) ≤ 2KT^{1−η₂/2}; the middle term is not stated; reason: n·rad(n)² ≥ σ²η₂ ln T is the bound that holds for the bonus (6) and that the proof needs (it is why part 1 assumes η₂ ≥ 4)
--   - reading: G = {θ_k ∈ CI_{t,k}, ∀(t,k)}, with CI_{t,k} not defined in the proof of Theorem 5 → for all k and 1 ≤ n ≤ T with n ≤ n_k: |Σ_{m≤n} ϵ_{t_k(m),k}|/n ≤ rad(n); reason: the confidence interval of an arm with n samples is its empirical mean ± rad(n), as in Algorithms 1–2
--   - generalization: η₁, η₂ ≥ 4 (part 1 of Theorem 5) → η₁, η₂ ≥ 0; reason: the bound holds for all nonnegative tuning parameters and specializes to part 1
--   - generalization: π = SE or π = UCB → any admissible policy; reason: the bound does not use the policy; it specializes to SE and UCB
--   - encoding: rounds t = 1, …, T and arms [K] → rounds 0, …, T − 1 (Lean round t is the paper's round t + 1) and Fin K; reason: Lean convention; same instances
-- source:
--   Simchi-Levi, Zheng, Zhu, A Simple and Optimal Policy Design with Safety against Heavy-Tailed Risk for Stochastic Bandits, arXiv:2206.02969v6, Online Appendix, proof of Theorem 5, part 1, p.17 (PDF p.54)

import Mathlib
import Definitions.Def_FoundationsRL_Bandits_pullCount
import Definitions.Def_LightTailBandit_IsNoiseModel
import Definitions.Def_LightTailBandit_reward
import Definitions.Def_LightTailBandit_pseudoRegret
import Definitions.Def_LightTailBandit_rad
import Definitions.Def_LightTailBandit_IsUCBRun
import Definitions.Def_LightTailBandit_IsSERun
import Definitions.Def_LightTailBandit_goodEvent

open MeasureTheory ProbabilityTheory FoundationsRL.Bandits

namespace LightTailBandit

/-- **`P(Ḡ) ≤ 2KT^{1−η₂/2}`** (Simchi-Levi, Zheng, Zhu, *A Simple and Optimal Policy Design with Safety against Heavy-Tailed Risk
for Stochastic Bandits*, arXiv:2206.02969v6, Online Appendix, proof of
Theorem 5, p.17 (PDF p.54): "`G = {θ_k ∈ CI_{t,k}, ∀(t,k)}`. Then `P(Ḡ) ≤ … ≤ 2KT^{1−η/2}`").

For every admissible policy and tuning parameters `η₁, η₂ ≥ 0`, the probability that some arm `k`
and some `1 ≤ n ≤ T` with `n ≤ n_k` have `|Σ_{m ≤ n} ϵ_{t_k(m),k}| / n > rad(n)` is at most
`2 K T^{1 − η₂/2}`.

**Formalization Note.** Rounds are 0-based (Lean round `t < T` is the paper's round `t + 1`), arms are `Fin K`, the
noise is a table `ε t k` with a filtration `ℱ` (`IsNoiseModel`), and σ-subGaussian is read as the
moment-generating-function condition with variance proxy `σ²`. The exponent's `η` is undefined in
Theorem 5's proof; it is read as `η₂`, the parameter that bounds `n · rad(n)² ≥ σ² η₂ ln T`. -/
theorem prob_not_good_event {Ω : Type*} [mΩ : MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ℱ : Filtration ℕ mΩ) {K T : ℕ} (hK : 2 ≤ K) (hT : 3 ≤ T) (hKT : K ≤ T)
    {σ η₁ η₂ : ℝ} (hσ : 0 < σ) (hη₁ : 0 ≤ η₁) (hη₂ : 0 ≤ η₂)
    (ε : ℕ → Fin K → Ω → ℝ) (a : ℕ → Ω → Fin K)
    (hε : IsNoiseModel μ ℱ T σ ε) (ha : IsAdaptedActions ℱ T a) :
    μ.real {ω | ¬ goodEvent σ η₁ η₂ T (ε · · ω) (a · ω)} ≤ 2 * K * (T : ℝ) ^ (1 - η₂ / 2) := by sorry

end LightTailBandit
