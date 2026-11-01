-- Prove2me | Theorems.Thm_LightTailBandit_pull_count_concentration
-- name    : LightTailBandit.pull_count_concentration
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T09:26:04.726985+00:00
-- url     : https://prove2.me/theorems/a5d4ea63-3098-4671-a065-87f0c0e6105f
-- title:
--   Proof of Lemma 2, App. p.1 — the mean of an arm's first $n$ noises concentrates: $P(\Sigma_k(n)\ge ny)\le e^{-ny^2/(2\sigma^2)}$
-- statement:
--   Throughout, $K\ge2$ arms and a horizon $T$ with $T\ge3$ and $T\ge K$ are fixed, $\sigma>0$, rounds are $t=1,\dots,T$, and the reward of round $t$ is $r_{t,a_t}=\theta_{a_t}+\epsilon_{t,a_t}$, where the noise $\epsilon_{t,k}$ of round $t$ and arm $k$ is independent of everything observed before round $t$ and is $\sigma$-sub-Gaussian: $\mathbb E[e^{\lambda\epsilon_{t,k}}]\le e^{\lambda^2\sigma^2/2}$ for all real $\lambda$. The action $a_t$ may depend only on the past (and on independent internal randomization). $n_k$ is the number of pulls of arm $k$ in the $T$ rounds, $\theta_*=\max_k\theta_k$, $\Delta_k=\theta_*-\theta_k\le1$, and the bonus is $\mathrm{rad}(n)=\sigma\sqrt{\ln T/n}\,\max\{\sqrt{\eta_1T/(nK)},\sqrt{\eta_2}\}$ (6).
--
--   For every admissible policy, every arm $k$, every $n\ge1$ and every $y\ge0$, the noise $\Sigma_k(n)=\sum_{m\le n}\epsilon_{t_k(m),k}$ of the first $n$ pulls of arm $k$ within the horizon satisfies
--   $$
--   P\big(\Sigma_k(n)\ge ny\big)\le\exp\left(-\frac{ny^2}{2\sigma^2}\right),\qquad P\big(\Sigma_k(n)\le-ny\big)\le\exp\left(-\frac{ny^2}{2\sigma^2}\right).
--   $$
--
--   The pull times $t_k(m)$ are chosen adaptively, so the $n$ noises are not a fixed sample; nevertheless their mean concentrates as if they were. This is the step the proof of Theorem 5 calls "concentration of subGaussian variables", used in every one of (19)–(26).
--
--   **Formalization Note** $\Sigma_k(n)$ is `armSum`; it adds the noises of the rounds before $T$ at which arm $k$ is pulled with fewer than $n$ earlier pulls, so it equals the paper's sum on $\{n_k\ge n\}$, and the bound holds without conditioning on that event.
--
--   Differences from the source:
--   - reading: ϵ_{t,k} is σ-subGaussian, glossed on p.8 as max{P(ϵ_{t,k} ≥ x), P(ϵ_{t,k} ≤ −x)} ≤ exp(−x²/(2σ²)) → E[exp(λ ε t k)] ≤ exp(λ²σ²/2) for every real λ (HasSubgaussianMGF with parameter σ²); reason: Lemma 1 and every 'concentration of subGaussian variables' step of the proof need the moment-generating-function bound, which the tail display does not imply (Lemma 1 fails under the display alone: two-point noise ±σ√(2 ln 2), T = 36, P(N ≥ 18a) = 135142796/2³⁶ > 2⁻⁹); the MGF condition is the standard meaning of σ-subGaussian and covers the Gaussian and bounded noises named on p.9
--   - generalization: noise ϵ_{t,k} sampled independently, zero mean, for each round and arm; the policy maps the history H_t (and its own randomization) to a_t → a noise table ε t k and a filtration ℱ with ε t k ℱ(t+1)-measurable and independent of ℱ t, and a t ℱ t-measurable; no independence across arms within a round is assumed; reason: the paper's model is the special case ℱ t = σ(noises of rounds before t, the policy's internal randomness up to t); only the independence of each round's noise from the past is used
--   - generalization: P(Σ_{n′≤n} ϵ_{t_2(n′),2}/n > δ) ≤ 2exp(−nδ²/(2σ²)) for arm 2 of a two-armed Gaussian instance → for any arm k, any admissible policy and any n ≥ 1, y ≥ 0: P(armSum k n ≥ n y) ≤ exp(−n y²/(2σ²)) and P(armSum k n ≤ −n y) ≤ exp(−n y²/(2σ²)), with no conditioning on n_k ≥ n; reason: the union of the two one-sided bounds gives the printed two-sided bound, '≥' is stronger than '>', and on {n_k ≥ n} armSum is the printed sum
--   - encoding: rounds t = 1, …, T and arms [K] → rounds 0, …, T − 1 (Lean round t is the paper's round t + 1) and Fin K; reason: Lean convention; same instances
-- source:
--   Simchi-Levi, Zheng, Zhu, A Simple and Optimal Policy Design with Safety against Heavy-Tailed Risk for Stochastic Bandits, arXiv:2206.02969v6, Online Appendix, proof of Lemma 2, p.1 (PDF p.38), last display; used in the proof of Theorem 5, pp.20–24

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

/-- **Concentration of an arm's first `n` noises** (Simchi-Levi, Zheng, Zhu, *A Simple and Optimal Policy Design with Safety against Heavy-Tailed Risk
for Stochastic Bandits*, arXiv:2206.02969v6, Online Appendix,
proof of Lemma 2, p.1 (PDF p.38): "`P(Σ_{n'=1}^n ϵ_{t_2(n'),2} / n > δ) ≤ 2exp(−nδ²/(2σ²))`"; used as
"concentration of subGaussian variables" in (19)–(26)).

For every admissible policy, every arm `k`, every `n ≥ 1` and every `y ≥ 0`, the noise
`Σ_{m ≤ n} ϵ_{t_k(m),k}` of the first `n` pulls of arm `k` within the horizon (`armSum`) satisfies
`P(armSum ≥ n y) ≤ exp(−n y²/(2σ²))` and `P(armSum ≤ −n y) ≤ exp(−n y²/(2σ²))`.

**Formalization Note.** Rounds are 0-based (Lean round `t < T` is the paper's round `t + 1`), arms are `Fin K`, the
noise is a table `ε t k` with a filtration `ℱ` (`IsNoiseModel`), and σ-subGaussian is read as the
moment-generating-function condition with variance proxy `σ²`. The bound is stated one-sided in each
direction and for the adaptively sampled pulls; a union of the two sides gives the printed
two-sided line. -/
theorem pull_count_concentration {Ω : Type*} [mΩ : MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ℱ : Filtration ℕ mΩ) {K T : ℕ} (hK : 2 ≤ K) (hT : 3 ≤ T) (hKT : K ≤ T)
    {σ : ℝ} (hσ : 0 < σ)
    (ε : ℕ → Fin K → Ω → ℝ) (a : ℕ → Ω → Fin K)
    (hε : IsNoiseModel μ ℱ T σ ε) (ha : IsAdaptedActions ℱ T a)
    (k : Fin K) (n : ℕ) (hn : 1 ≤ n) (y : ℝ) (hy : 0 ≤ y) :
    μ.real {ω | n * y ≤ armSum T (ε · · ω) (a · ω) k n} ≤ Real.exp (-(n * y ^ 2) / (2 * σ ^ 2)) ∧
      μ.real {ω | armSum T (ε · · ω) (a · ω) k n ≤ -(n * y)} ≤
        Real.exp (-(n * y ^ 2) / (2 * σ ^ 2)) := by sorry

end LightTailBandit
