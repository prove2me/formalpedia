-- Prove2me | Theorems.Thm_KaufmannTS_Bernoulli_regret_eq_sum_gap_mul_plays
-- name    : KaufmannTS.Bernoulli.regret_eq_sum_gap_mul_plays
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T11:25:07.920016+00:00
-- url     : https://prove2.me/theorems/d82ea333-187b-4aed-abb5-cf310c7d0f50
-- title:
--   Eq. (1), p. 1 — $\mathcal R(T) = T\mu^* - \mathbb E[\sum_t R_t] = \sum_a (\mu^* - \mu_a)\,\mathbb E[N_{a,T}]$
-- statement:
--   Consider Thompson Sampling with uniform priors on a $K$-armed Bernoulli bandit ($K\ge2$) with means in $(0,1)$ and unique optimal arm $1$, so that $\mu^*=\max_a\mu_a=\mu_1$. Let $R_t$ be the reward received in round $t$ and $\mathcal R(T)$ the expected regret over $T$ rounds. For every horizon $T$,
--   $$\mathcal R(T)=T\mu^*-\mathbb E\Big[\sum_{t=1}^{T}R_t\Big]=\sum_{a=1}^{K}(\mu^*-\mu_a)\,\mathbb E[N_{a,T}],$$
--   where $N_{a,T}$ is the number of draws of arm $a$ in rounds $1,\dots,T$.
--
--   This identity turns the per-arm bound of Theorem 2 into the regret bound of Theorem 1.
--
--   **Formalization Note** $\mathcal R(T)$ is the published Thompson Sampling model's expected regret $\mathbb E\big[\sum_{t=1}^{T}(\mu^*-\mu_{A_t})\big]$; the first equality is stated without subtraction, as $\mathbb E[\sum_{t=1}^T R_t]+\mathcal R(T)=T\mu^*$, so that the paper's definition $T\mu^*-\mathbb E[\sum_t R_t]$ is part of the statement. The page's last factor reads $\mathbb E[N_{a,t}]$, a typo for $\mathbb E[N_{a,T}]$. Expectations are lower integrals in $[0,\infty]$. Lean arm $0$ is the paper's arm $1$.
-- source:
--   Kaufmann, Korda, Munos, Thompson Sampling: An Asymptotically Optimal Finite Time Analysis, arXiv:1205.4217v2, p. 1, Eq. (1)

import Mathlib
import Definitions.Def_KaufmannTS_Bernoulli_Model
open MeasureTheory ProbabilityTheory BanditAlgorithm AgrawalGoyalTS.TwoArmed
open scoped ENNReal

namespace KaufmannTS.Bernoulli

/-- Eq. (1), p. 1: the regret of Thompson Sampling, `R(T) := T μ* - E[∑_{t=1}^T R_t]`, decomposes over
arms, `R(T) = ∑_a (μ* - μ_a) E[N_{a,T}]`. The first conjunct is the first equality of (1), written
without subtraction as `E[∑_t R_t] + R(T) = T μ*`, where `R(T)` is the published model's regret
`tsRegret` and `R_t = tsReward ω t` is the reward observed in Lean round `t` (paper round `t + 1`);
the second conjunct is the second equality. Lean arm `0` is the paper's arm `1` (the unique optimal arm,
so `μ* = μ 0`); `tsPlays ω T a` counts the plays of arm `a` in Lean rounds `0, …, T-1`, i.e. in paper
rounds `1, …, T`. -/
theorem regret_eq_sum_gap_mul_plays {K : ℕ} [NeZero K] (hK : 2 ≤ K) (μ : Fin K → ℝ)
    (hμ : ∀ a, μ a ∈ Set.Ioo (0 : ℝ) 1) (hopt : ∀ a, a ≠ 0 → μ a < μ 0) (T : ℕ) :
    ((∫⁻ ω, ∑ t ∈ Finset.range T, ENNReal.ofReal (tsReward ω t) ∂(tsLaw (bernoulliInstance μ hμ))) +
        tsRegret (bernoulliInstance μ hμ) T = ENNReal.ofReal ((T : ℝ) * μ 0)) ∧
    tsRegret (bernoulliInstance μ hμ) T =
      ∑ a : Fin K, ENNReal.ofReal (μ 0 - μ a) *
        ∫⁻ ω, (tsPlays ω T a : ℝ≥0∞) ∂(tsLaw (bernoulliInstance μ hμ)) := by sorry

end KaufmannTS.Bernoulli
