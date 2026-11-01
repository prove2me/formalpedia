-- Prove2me | Theorems.Thm_LightTailBandit_lemma_1
-- name    : LightTailBandit.lemma_1
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T09:25:54.516729+00:00
-- url     : https://prove2.me/theorems/3f77e6d6-0b6b-459b-a6b0-8e91b4a6e8d8
-- title:
--   Lemma 1 — the genuine noise has mean $0$ and a sub-Gaussian tail with proxy $\sigma^2T$ (corrected: MGF sub-Gaussian noise)
-- statement:
--   Throughout, $K\ge2$ arms and a horizon $T$ with $T\ge3$ and $T\ge K$ are fixed, $\sigma>0$, rounds are $t=1,\dots,T$, and the reward of round $t$ is $r_{t,a_t}=\theta_{a_t}+\epsilon_{t,a_t}$, where the noise $\epsilon_{t,k}$ of round $t$ and arm $k$ is independent of everything observed before round $t$ and is $\sigma$-sub-Gaussian: $\mathbb E[e^{\lambda\epsilon_{t,k}}]\le e^{\lambda^2\sigma^2/2}$ for all real $\lambda$. The action $a_t$ may depend only on the past (and on independent internal randomization). $n_k$ is the number of pulls of arm $k$ in the $T$ rounds, $\theta_*=\max_k\theta_k$, $\Delta_k=\theta_*-\theta_k\le1$, and the bonus is $\mathrm{rad}(n)=\sigma\sqrt{\ln T/n}\,\max\{\sqrt{\eta_1T/(nK)},\sqrt{\eta_2}\}$ (6).
--
--   **Lemma 1.** For every admissible policy, the genuine noise $N(T)=\sum_{t=1}^T\epsilon_{t,a_t}$ is integrable, satisfies $\mathbb E[N(T)]=0$ and, for every $x\ge0$,
--   $$
--   \max\{P(N(T)\ge x),\,P(N(T)\le-x)\}\le\exp\left(-\frac{x^2}{2\sigma^2T}\right).
--   $$
--
--   Since $\hat R(T)=R(T)-N(T)$, the lemma reduces the tail of the empirical regret to the tail of the pseudo regret, up to a sub-Gaussian term; it gives the first exponential of Theorem 5.
--
--   **Formalization Note** The noise is a table with a filtration (`IsNoiseModel`) and the actions are adapted (`IsAdaptedActions`); the tails are stated separately.
--
--   Differences from the source:
--   - correction: ϵ_{t,k} σ-subGaussian in the tail sense max{P(ϵ_{t,k} ≥ x), P(ϵ_{t,k} ≤ −x)} ≤ exp(−x²/(2σ²)) (p.8) → E[exp(λ ε t k)] ≤ exp(λ²σ²/2) for every real λ (HasSubgaussianMGF with parameter σ²); reason: under the tail display alone the lemma is false: K = 2, T = 36, any policy, independent ϵ_{t,k} = ±a with probability 1/2 each, a = σ√(2 ln 2), satisfy every assumption of p.8 (P(ϵ ≥ x) = 1/2 = exp(−a²/(2σ²)) ≤ exp(−x²/(2σ²)) for 0 < x ≤ a, and 0 for x > a); N(36) has the law of a(2B − 36) with B ~ Bin(36, 1/2), and P(N ≥ 18a) = P(B ≥ 27) = 135142796/2³⁶ ≈ 0.0019666 > 2⁻⁹ = exp(−(18a)²/(72σ²)) ≈ 0.0019531
--   - generalization: noise ϵ_{t,k} sampled independently, zero mean, for each round and arm; the policy maps the history H_t (and its own randomization) to a_t → a noise table ε t k and a filtration ℱ with ε t k ℱ(t+1)-measurable and independent of ℱ t, and a t ℱ t-measurable; no independence across arms within a round is assumed; reason: the paper's model is the special case ℱ t = σ(noises of rounds before t, the policy's internal randomness up to t); only the independence of each round's noise from the past is used
--   - encoding: E[N(T)] = 0 → N(T) is integrable and ∫ N(T) dμ = 0; reason: the expectation in the lemma exists; stating integrability excludes Lean's value 0 for the integral of a non-integrable function
--   - reading: x unquantified → every x ≥ 0; reason: for x < 0 the bound fails trivially (the right side is below 1 while P(N ≥ x) can be near 1)
--   - encoding: rounds t = 1, …, T and arms [K] → rounds 0, …, T − 1 (Lean round t is the paper's round t + 1) and Fin K; reason: Lean convention; same instances
-- source:
--   Simchi-Levi, Zheng, Zhu, A Simple and Optimal Policy Design with Safety against Heavy-Tailed Risk for Stochastic Bandits, arXiv:2206.02969v6, Lemma 1, p.9

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

/-- **Lemma 1** (Simchi-Levi, Zheng, Zhu, *A Simple and Optimal Policy Design with Safety against Heavy-Tailed Risk
for Stochastic Bandits*, arXiv:2206.02969v6, Lemma 1, p.9), with the
noise condition read as the sub-Gaussian MGF bound (corrected hypothesis).

For every admissible policy, the genuine noise `N(T) = Σ_t ϵ_{t,a_t}` is integrable with mean `0`, and for every
`x ≥ 0`, `P(N(T) ≥ x) ≤ exp(−x²/(2σ²T))` and `P(N(T) ≤ −x) ≤ exp(−x²/(2σ²T))`.

**Formalization Note.** Rounds are 0-based (Lean round `t < T` is the paper's round `t + 1`), arms are `Fin K`, the
noise is a table `ε t k` with a filtration `ℱ` (`IsNoiseModel`), and σ-subGaussian is read as the
moment-generating-function condition with variance proxy `σ²`. Under the tail display of p.8 alone the
lemma is false (two-point noise, `T = 36`), hence the MGF hypothesis. `x` is nonnegative. -/
theorem lemma_1 {Ω : Type*} [mΩ : MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ℱ : Filtration ℕ mΩ) {K T : ℕ} (hK : 2 ≤ K) (hT : 3 ≤ T) (hKT : K ≤ T)
    {σ : ℝ} (hσ : 0 < σ)
    (ε : ℕ → Fin K → Ω → ℝ) (a : ℕ → Ω → Fin K)
    (hε : IsNoiseModel μ ℱ T σ ε) (ha : IsAdaptedActions ℱ T a) :
    Integrable (fun ω => genuineNoise T (ε · · ω) (a · ω)) μ ∧
    (∫ ω, genuineNoise T (ε · · ω) (a · ω) ∂μ = 0) ∧
      ∀ x : ℝ, 0 ≤ x →
        μ.real {ω | x ≤ genuineNoise T (ε · · ω) (a · ω)} ≤ Real.exp (-x ^ 2 / (2 * σ ^ 2 * T)) ∧
        μ.real {ω | genuineNoise T (ε · · ω) (a · ω) ≤ -x} ≤ Real.exp (-x ^ 2 / (2 * σ ^ 2 * T)) := by sorry

end LightTailBandit
