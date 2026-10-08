-- Prove2me | Theorems.Thm_KaufmannTS_Bernoulli_thompson_sampling_regret_bound
-- name    : KaufmannTS.Bernoulli.thompson_sampling_regret_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T11:25:40.6715+00:00
-- url     : https://prove2.me/theorems/18fe6530-0e81-4c55-8ec1-dc44931e6d08
-- title:
--   Theorem 1, p. 3 — Bernoulli Thompson Sampling has regret $(1+\epsilon)\sum_a \Delta_a(\ln T+\ln\ln T)/K(\mu_a,\mu^*) + C$
-- statement:
--   Consider a $K$-armed bandit ($K\ge2$) in which arm $a$ pays a Bernoulli reward of mean $\mu_a\in(0,1)$, and arm $1$ is the unique optimal arm: $\mu^*=\mu_1>\mu_a$ for $a\neq1$. Run Thompson Sampling with uniform priors, and let $\mathcal R(T)$ be its expected regret over $T$ rounds. For every $\epsilon>0$ there is a constant $C$, depending on $\epsilon$ and the instance, such that for every horizon $T$,
--   $$\mathcal R(T)\le(1+\epsilon)\sum_{a:\,\mu_a\neq\mu^*}\frac{\Delta_a\big(\ln T+\ln\ln T\big)}{K(\mu_a,\mu^*)}+C,$$
--   where $\Delta_a=\mu^*-\mu_a$ and $K(p,q)=p\ln\frac pq+(1-p)\ln\frac{1-p}{1-q}$ is the Kullback–Leibler divergence between Bernoulli distributions.
--
--   The leading term matches the Lai–Robbins lower bound $\liminf_T\mathcal R(T)/\ln T\ge\sum_a\Delta_a/K(\mu_a,\mu^*)$ for consistent policies, so Thompson Sampling is asymptotically optimal for Bernoulli rewards.
--
--   **Formalization Note** The regret is the published Thompson Sampling model's $\mathbb E[\sum_{t=1}^T(\mu^*-\mu_{A_t})]$ in $[0,\infty]$, compared with the real right-hand side through its embedding. The constant is chosen after the instance and $\epsilon$ and before $T$; small horizons, where $\ln\ln T$ is negative or Lean's $\ln0=0$, are absorbed by it. Unique optimality of arm $1$ is the standing assumption of §2 (p. 3); the paper's reduction of several optimal arms to one is cited from Agrawal–Goyal and is not part of this statement. The hypotheses $0<\mu_a<1$ for every arm and $K\ge2$ are added: at $\mu^*=1$ the divergence $K(\mu_a,\mu^*)$ is infinite and the proof divides by $\mu_1(1-\mu_1)$. Lean arm $0$ is the paper's arm $1$, so the sum ranges over the arms whose mean differs from that of arm $0$.
-- source:
--   Kaufmann, Korda, Munos, Thompson Sampling: An Asymptotically Optimal Finite Time Analysis, arXiv:1205.4217v2, p. 3, Theorem 1 (regret Eq. (1), p. 1; standing assumptions §2, p. 3)

import Mathlib
import Definitions.Def_KaufmannTS_Bernoulli_Model
open MeasureTheory ProbabilityTheory BanditAlgorithm AgrawalGoyalTS.TwoArmed
open scoped ENNReal

namespace KaufmannTS.Bernoulli

/-- Theorem 1, p. 3: Thompson Sampling with uniform priors on a Bernoulli bandit with means in
`(0,1)` and a unique optimal arm (Lean arm `0`, the paper's arm `1`, so `μ* = μ 0`) satisfies, for every
`ε > 0` and some constant `C` depending on `ε` and the instance, for every horizon `T`,
`R(T) ≤ (1+ε) ∑_{a : μ_a ≠ μ*} Δ_a (ln T + ln ln T)/K(μ_a, μ*) + C`, `Δ_a = μ* - μ_a`. -/
theorem thompson_sampling_regret_bound {K : ℕ} [NeZero K] (hK : 2 ≤ K) (μ : Fin K → ℝ)
    (hμ : ∀ a, μ a ∈ Set.Ioo (0 : ℝ) 1) (hopt : ∀ a, a ≠ 0 → μ a < μ 0)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, ∀ T : ℕ,
      tsRegret (bernoulliInstance μ hμ) T ≤
        ENNReal.ofReal ((1 + ε) *
            ∑ a ∈ Finset.univ.filter (fun a : Fin K => μ a ≠ μ 0),
              (μ 0 - μ a) * (Real.log T + Real.log (Real.log T)) /
                bernoulliRelativeEntropy (μ a) (μ 0) + C) := by sorry

end KaufmannTS.Bernoulli
