-- Prove2me | Theorems.Thm_LightTailBandit_eq_26
-- name    : LightTailBandit.eq_26
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T09:26:06.642971+00:00
-- url     : https://prove2.me/theorems/e5dc408b-c2a5-4bab-92ff-031c1685e285
-- title:
--   (26), App. p.24 — UCB, $k\notin\mathcal A_0$: probability at most $\exp(-(x-2K-8\sigma\sqrt{(\eta_1\vee\eta_2)KT\ln T})_+^2/(128\sigma^2KT))+T\exp(-(x-2K)_+\sqrt{\eta_1\ln T}/(16\sigma\sqrt{KT}))$
-- statement:
--   Throughout, $K\ge2$ arms and a horizon $T$ with $T\ge3$ and $T\ge K$ are fixed, $\sigma>0$, rounds are $t=1,\dots,T$, and the reward of round $t$ is $r_{t,a_t}=\theta_{a_t}+\epsilon_{t,a_t}$, where the noise $\epsilon_{t,k}$ of round $t$ and arm $k$ is independent of everything observed before round $t$ and is $\sigma$-sub-Gaussian: $\mathbb E[e^{\lambda\epsilon_{t,k}}]\le e^{\lambda^2\sigma^2/2}$ for all real $\lambda$. The action $a_t$ may depend only on the past (and on independent internal randomization). $n_k$ is the number of pulls of arm $k$ in the $T$ rounds, $\theta_*=\max_k\theta_k$, $\Delta_k=\theta_*-\theta_k\le1$, and the bonus is $\mathrm{rad}(n)=\sigma\sqrt{\ln T/n}\,\max\{\sqrt{\eta_1T/(nK)},\sqrt{\eta_2}\}$ (6).
--
--   Let $\eta_1>0$, $\eta_2\ge0$, $x\ge2K$, let $b$ be an optimal arm and $k\ne b$. For UCB with the bonus (6),
--   $$
--   P\Big(\Delta_k\ge\tfrac{x-2K}{4T},\ k\notin\mathcal A_0\Big)\le \exp\left(-\frac{\big(x-2K-8\sigma\sqrt{(\eta_1\vee\eta_2)KT\ln T}\big)_+^2}{128\sigma^2KT}\right)+T\,\exp\left(-\frac{(x-2K)_+\sqrt{\eta_1\ln T}}{16\sigma\sqrt{KT}}\right).
--   $$
--
--   This is the second of the two terms of the UCB decomposition; summed over the arms with (25), it gives the second and third exponentials of Theorem 5.
--
--   **Formalization Note** $n_k-1$ is real subtraction and $(\cdot)_+=\max(\cdot,0)$, applied before squaring. The run predicate holds on every sample path.
--
--   Differences from the source:
--   - reading: ϵ_{t,k} is σ-subGaussian, glossed on p.8 as max{P(ϵ_{t,k} ≥ x), P(ϵ_{t,k} ≤ −x)} ≤ exp(−x²/(2σ²)) → E[exp(λ ε t k)] ≤ exp(λ²σ²/2) for every real λ (HasSubgaussianMGF with parameter σ²); reason: Lemma 1 and every 'concentration of subGaussian variables' step of the proof need the moment-generating-function bound, which the tail display does not imply (Lemma 1 fails under the display alone: two-point noise ±σ√(2 ln 2), T = 36, P(N ≥ 18a) = 135142796/2³⁶ > 2⁻⁹); the MGF condition is the standard meaning of σ-subGaussian and covers the Gaussian and bounded noises named on p.9
--   - generalization: noise ϵ_{t,k} sampled independently, zero mean, for each round and arm; the policy maps the history H_t (and its own randomization) to a_t → a noise table ε t k and a filtration ℱ with ε t k ℱ(t+1)-measurable and independent of ℱ t, and a t ℱ t-measurable; no independence across arms within a round is assumed; reason: the paper's model is the special case ℱ t = σ(noises of rounds before t, the policy's internal randomness up to t); only the independence of each round's noise from the past is used
--   - generalization: Algorithm 2 'randomly select[s] one if a tie happens' → IsUCBRun: any tie-break, deterministic or randomized, on every sample path; reason: every run of Algorithm 2 satisfies the predicate; the proof never uses the tie rule
--   - reading: UCB index θ̂_{t−1,k} + rad(n_{t−1,k}) at an unpulled arm (rad(0) undefined) → while some arm is unpulled, UCB pulls an unpulled arm (the convention rad(0) = +∞); reason: the page leaves the index of an unsampled arm undefined; the proof uses that arm 1 has been sampled when arm k is pulled for the (n₀+1)-st time
--   - generalization: arm 1 is the optimal arm (WLOG), k ≠ 1 → b is any arm with θ b = θ_*, k ≠ b; reason: with several optimal arms every choice of b is covered; it specializes to the paper's arm 1
--   - encoding: Let x ≥ 2K (part 2 of the proof) → 2K ≤ x as a hypothesis; reason: as printed
--   - encoding: rounds t = 1, …, T and arms [K] → rounds 0, …, T − 1 (Lean round t is the paper's round t + 1) and Fin K; reason: Lean convention; same instances
--   - encoding: (n_k − 1)∆_k ≥ (n_k − 1)(x − 2K)/(4T), k ∉ A₀ → Δ_k ≥ (x − 2K)/(4T) and k ∉ A₀; reason: off A₀, n_k > 1 + T/K > 1, so the two events coincide
-- source:
--   Simchi-Levi, Zheng, Zhu, A Simple and Optimal Policy Design with Safety against Heavy-Tailed Risk for Stochastic Bandits, arXiv:2206.02969v6, Online Appendix, proof of Theorem 5, part 2(b), p.24 (PDF p.61), eq. (26)

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

/-- **(26): UCB, `k ∉ A₀`** (Simchi-Levi, Zheng, Zhu, *A Simple and Optimal Policy Design with Safety against Heavy-Tailed Risk
for Stochastic Bandits*, arXiv:2206.02969v6, Online Appendix, proof of Theorem 5, part 2(b), p.24 (PDF p.61), eq. (26)).

For UCB with the bonus (6), `η₁ > 0`, `η₂ ≥ 0`, `x ≥ 2K` and an arm `k ≠ b`:
`P(Δ_k ≥ (x−2K)/(4T), k ∉ A₀) ≤ exp(−(x − 2K − 8σ√(max(η₁,η₂)KT ln T))₊² / (128σ²KT)) + T exp(−(x − 2K)₊ √(η₁ ln T) / (16σ√(KT)))`.

**Formalization Note.** Rounds are 0-based (Lean round `t < T` is the paper's round `t + 1`), arms are `Fin K`, the
noise is a table `ε t k` with a filtration `ℱ` (`IsNoiseModel`), and σ-subGaussian is read as the
moment-generating-function condition with variance proxy `σ²`. `b` is any optimal arm (the paper's
"arm 1"), `n_k = pullCount (a · ω) T k`, and `n_k − 1` is real subtraction. The page's event `(n_k−1)Δ_k ≥ (n_k−1)(x−2K)/(4T)` equals `Δ_k ≥ (x−2K)/(4T)` since `n_k > 1` off `A₀`. -/
theorem eq_26 {Ω : Type*} [mΩ : MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ℱ : Filtration ℕ mΩ) {K T : ℕ} (hK : 2 ≤ K) (hT : 3 ≤ T) (hKT : K ≤ T)
    {σ η₁ η₂ : ℝ} (hσ : 0 < σ) (hη₁ : 0 < η₁) (hη₂ : 0 ≤ η₂)
    (θ : Fin K → ℝ) (hgap : ∀ k, gap θ k ≤ 1)
    (ε : ℕ → Fin K → Ω → ℝ) (a : ℕ → Ω → Fin K)
    (hε : IsNoiseModel μ ℱ T σ ε) (ha : IsAdaptedActions ℱ T a)
    (hrun : ∀ ω, IsUCBRun σ η₁ η₂ T θ (ε · · ω) (a · ω))
    (x : ℝ) (hx : 2 * K ≤ x) (b k : Fin K) (hb : θ b = θstar θ) (hkb : k ≠ b) :
    μ.real {ω | (x - 2 * K) / (4 * T) ≤ gap θ k ∧ ¬ inA0 T (a · ω) b k} ≤
      Real.exp (-(max (x - 2 * K - 8 * σ * Real.sqrt (max η₁ η₂ * K * T * Real.log T)) 0) ^ 2 /
        (128 * σ ^ 2 * K * T)) +
        T * Real.exp (-(max (x - 2 * K) 0 * Real.sqrt (η₁ * Real.log T)) /
        (16 * σ * Real.sqrt ((K : ℝ) * T))) := by sorry

end LightTailBandit
