-- Prove2me | Theorems.Thm_LightTailBandit_theorem_5
-- name    : LightTailBandit.theorem_5
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T09:26:06.3309+00:00
-- url     : https://prove2.me/theorems/42652d50-a784-4b15-8667-4cc14a5b9d7a
-- title:
--   Theorem 5 — SE and UCB with the bonus (6) have expected regret $4K+8\sigma\sqrt{(\eta_1\vee\eta_2)KT\ln T}$ and a regret tail $e^{-\Omega(x/\sqrt{KT})}$ for every $x>0$
-- statement:
--   Throughout, $K\ge2$ arms and a horizon $T$ with $T\ge3$ and $T\ge K$ are fixed, $\sigma>0$, rounds are $t=1,\dots,T$, and the reward of round $t$ is $r_{t,a_t}=\theta_{a_t}+\epsilon_{t,a_t}$, where the noise $\epsilon_{t,k}$ of round $t$ and arm $k$ is independent of everything observed before round $t$ and is $\sigma$-sub-Gaussian: $\mathbb E[e^{\lambda\epsilon_{t,k}}]\le e^{\lambda^2\sigma^2/2}$ for all real $\lambda$. The action $a_t$ may depend only on the past (and on independent internal randomization). $n_k$ is the number of pulls of arm $k$ in the $T$ rounds, $\theta_*=\max_k\theta_k$, $\Delta_k=\theta_*-\theta_k\le1$, and the bonus is $\mathrm{rad}(n)=\sigma\sqrt{\ln T/n}\,\max\{\sqrt{\eta_1T/(nK)},\sqrt{\eta_2}\}$ (6).
--
--   **Theorem 5.** For the $K$-armed bandit problem, both the policy $\pi=\mathrm{SE}$ (Algorithm 1) and the policy $\pi=\mathrm{UCB}$ (Algorithm 2) with the bonus
--   $$
--   \mathrm{rad}(n)=\sigma\sqrt{\frac{\ln T}{n}}\cdot\max\left\{\sqrt{\frac{\eta_1T}{nK}},\sqrt{\eta_2}\right\}
--   $$
--   satisfy the following two properties, for every mean vector $\theta$ with $\Delta_k\le1$ for all $k$:
--
--   1. if $\eta_1,\eta_2\ge4$, then $R(T)$ is integrable and $\mathbb E[R(T)]\le4K+8\sigma\sqrt{\max\{\eta_1,\eta_2\}KT\ln T}$;
--   2. if $\eta_1>0$, $\eta_2\ge0$, then for every $x>0$,
--   $$
--   P\big(\hat R(T)\ge x\big)\le\exp\left(-\frac{x^2}{8K\sigma^2T}\right)+4K\exp\left(-\frac{\big(x-2K-8\sigma\sqrt{(\eta_1\vee\eta_2)KT\ln T}\big)_+^2}{128\sigma^2KT}\right)+2K^2T\exp\left(-\frac{(x-2K)_+\sqrt{\eta_1\ln T}}{16\sigma\sqrt{KT}}\right).
--   $$
--
--   Part 1 is the minimax-optimal $O(\sqrt{KT\ln T})$ expected regret. Part 2 says that the probability of a regret of order $x$ decays like $e^{-\Omega(x/\sqrt{KT})}$, uniformly over instances; in particular the probability of linear regret is $e^{-\Omega(\sqrt T)}$, whereas for standard UCB and SE it decays only polynomially in $T$.
--
--   **Formalization Note** The policy is a run predicate holding on every sample path, so the bound covers every tie-breaking rule and every order inside an SE phase. $\mathbb E[R(T)]$ is a Bochner integral of a bounded measurable function (proved in the verification file), and $(\cdot)_+$ is applied before squaring.
--
--   Differences from the source:
--   - reading: ϵ_{t,k} is σ-subGaussian, glossed on p.8 as max{P(ϵ_{t,k} ≥ x), P(ϵ_{t,k} ≤ −x)} ≤ exp(−x²/(2σ²)) → E[exp(λ ε t k)] ≤ exp(λ²σ²/2) for every real λ (HasSubgaussianMGF with parameter σ²); reason: Lemma 1 and every 'concentration of subGaussian variables' step of the proof need the moment-generating-function bound, which the tail display does not imply (Lemma 1 fails under the display alone: two-point noise ±σ√(2 ln 2), T = 36, P(N ≥ 18a) = 135142796/2³⁶ > 2⁻⁹); the MGF condition is the standard meaning of σ-subGaussian and covers the Gaussian and bounded noises named on p.9
--   - generalization: noise ϵ_{t,k} sampled independently, zero mean, for each round and arm; the policy maps the history H_t (and its own randomization) to a_t → a noise table ε t k and a filtration ℱ with ε t k ℱ(t+1)-measurable and independent of ℱ t, and a t ℱ t-measurable; no independence across arms within a round is assumed; reason: the paper's model is the special case ℱ t = σ(noises of rounds before t, the policy's internal randomness up to t); only the independence of each round's noise from the past is used
--   - generalization: Algorithm 1 pulls each arm of A once per phase, in an unspecified order → IsSERun: any order inside a phase, deterministic or randomized, on every sample path; reason: every run of Algorithm 1 satisfies the predicate; the order inside a phase does not enter the regret bound
--   - generalization: Algorithm 2 'randomly select[s] one if a tie happens' → IsUCBRun: any tie-break, deterministic or randomized, on every sample path; reason: every run of Algorithm 2 satisfies the predicate; the proof never uses the tie rule
--   - reading: UCB index θ̂_{t−1,k} + rad(n_{t−1,k}) at an unpulled arm (rad(0) undefined) → while some arm is unpulled, UCB pulls an unpulled arm (the convention rad(0) = +∞); reason: the page leaves the index of an unsampled arm undefined; the proof uses that arm 1 has been sampled when arm k is pulled for the (n₀+1)-st time
--   - reading: Algorithm 1, line 3: pull each arm in A once, even if this overruns T → the run stops at round T; a last phase may be cut short and does no elimination; reason: the regret counts exactly T rounds
--   - reading: line 4: eliminate k if ∃k′: θ̂_{t_{k′}(n),k′} − rad(n_{t,k′}) > θ̂_{t_k(n),k} + rad(n_{t,k}) → k′ ranges over the current active set, all eliminations of a phase use the same estimates, and both radii are rad(n) since every active arm has n pulls; reason: an eliminated arm has no n-th sample, so θ̂_{t_{k′}(n),k′} is defined only for active k′; the pull-count invariant is proved in the verification file
--   - encoding: sup_θ of the expected regret / of the tail probability, with ∆_k ≤ 1 (∀k ∈ [N]) → the bound for every θ : Fin K → ℝ with gap θ k ≤ 1 for all k; reason: a bound on a supremum is the same as the bound for every θ; '[N]' on p.8 is a misprint for [K]
--   - encoding: both π = SE and π = UCB satisfy the two properties → one action process a with the hypothesis (∀ω, IsSERun …) ∨ (∀ω, IsUCBRun …); reason: a statement for every run of either policy is the same as a statement for each policy
--   - encoding: E[R^π_θ] ≤ 4K + 8σ√(…) → R(T) is integrable and ∫ R(T) dμ ≤ 4K + 8σ√(…); reason: the expectation exists (R is bounded by T); stating integrability excludes Lean's value 0 for the integral of a non-integrable function
--   - encoding: rounds t = 1, …, T and arms [K] → rounds 0, …, T − 1 (Lean round t is the paper's round t + 1) and Fin K; reason: Lean convention; same instances
-- source:
--   Simchi-Levi, Zheng, Zhu, A Simple and Optimal Policy Design with Safety against Heavy-Tailed Risk for Stochastic Bandits, arXiv:2206.02969v6, Theorem 5, p.19

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

/-- **Theorem 5** (Simchi-Levi, Zheng, Zhu, *A Simple and Optimal Policy Design with Safety against Heavy-Tailed Risk
for Stochastic Bandits*, arXiv:2206.02969v6, Theorem 5, p.19).

For the `K`-armed bandit (`K ≥ 2`, `T ≥ 3`, `T ≥ K`, noise parameter `σ > 0`, every mean vector
`θ` with gaps `Δ_k ≤ 1`), both successive elimination and UCB with the bonus
`rad(n) = σ√(ln T/n) · max{√(η₁T/(nK)), √η₂}` (6) satisfy:
1. if `η₁, η₂ ≥ 4`, then `E[R(T)] ≤ 4K + 8σ√(max{η₁,η₂} K T ln T)`;
2. if `η₁ > 0, η₂ ≥ 0`, then for every `x > 0`,
   `P(R̂(T) ≥ x) ≤ exp(−x²/(8Kσ²T)) + 4K exp(−(x − 2K − 8σ√((η₁∨η₂)KT ln T))₊²/(128σ²KT))
     + 2K²T exp(−(x − 2K)₊ √(η₁ ln T)/(16σ√(KT)))`.

**Formalization Note.** Rounds are 0-based (Lean round `t < T` is the paper's round `t + 1`), arms are `Fin K`, the
noise is a table `ε t k` with a filtration `ℱ` (`IsNoiseModel`), and σ-subGaussian is read as the
moment-generating-function condition with variance proxy `σ²`. The policy is given as a run predicate
holding on every sample path (`IsSERun` or `IsUCBRun`), which leaves the order within an SE phase
and the UCB tie-break free; UCB pulls every unpulled arm first (`rad(0) = +∞`), and SE stops at
round `T`. The supremum over `θ` is the bound for every `θ` with gaps at most `1`. -/
theorem theorem_5 {Ω : Type*} [mΩ : MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ℱ : Filtration ℕ mΩ) {K T : ℕ} (hK : 2 ≤ K) (hT : 3 ≤ T) (hKT : K ≤ T)
    {σ : ℝ} (hσ : 0 < σ) (η₁ η₂ : ℝ)
    (θ : Fin K → ℝ) (hgap : ∀ k, gap θ k ≤ 1)
    (ε : ℕ → Fin K → Ω → ℝ) (a : ℕ → Ω → Fin K)
    (hε : IsNoiseModel μ ℱ T σ ε) (ha : IsAdaptedActions ℱ T a)
    (hrun : (∀ ω, IsSERun σ η₁ η₂ T θ (ε · · ω) (a · ω)) ∨
      (∀ ω, IsUCBRun σ η₁ η₂ T θ (ε · · ω) (a · ω))) :
    (4 ≤ η₁ → 4 ≤ η₂ →
      Integrable (fun ω => pseudoRegret θ T (a · ω)) μ ∧
      ∫ ω, pseudoRegret θ T (a · ω) ∂μ ≤
        4 * K + 8 * σ * Real.sqrt (max η₁ η₂ * K * T * Real.log T)) ∧
    (0 < η₁ → 0 ≤ η₂ → ∀ x : ℝ, 0 < x →
      μ.real {ω | x ≤ empiricalRegret θ T (ε · · ω) (a · ω)} ≤
        Real.exp (-x ^ 2 / (8 * K * σ ^ 2 * T)) +
          4 * K * Real.exp (-(max (x - 2 * K - 8 * σ * Real.sqrt (max η₁ η₂ * K * T * Real.log T)) 0) ^ 2 /
            (128 * σ ^ 2 * K * T)) +
          2 * (K : ℝ) ^ 2 * T * Real.exp (-(max (x - 2 * K) 0 * Real.sqrt (η₁ * Real.log T)) /
            (16 * σ * Real.sqrt ((K : ℝ) * T)))) := by sorry

end LightTailBandit
