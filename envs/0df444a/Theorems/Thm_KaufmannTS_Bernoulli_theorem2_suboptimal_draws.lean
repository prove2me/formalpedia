-- Prove2me | Theorems.Thm_KaufmannTS_Bernoulli_theorem2_suboptimal_draws
-- name    : KaufmannTS.Bernoulli.theorem2_suboptimal_draws
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T11:24:48.379162+00:00
-- url     : https://prove2.me/theorems/39c649b3-8bc9-4516-a972-00d1e30ee5f3
-- title:
--   Theorem 2, p. 4 — $\mathbb E[N_{a,T}] \le (1+\epsilon)(\ln T + \ln\ln T)/K(\mu_a,\mu_1) + C$
-- statement:
--   Consider Thompson Sampling with uniform priors on a $K$-armed Bernoulli bandit ($K\ge2$) with means in $(0,1)$ and unique optimal arm $1$. Let $\epsilon>0$ and let $a\neq1$ be a suboptimal arm. There is a constant $C$ such that for every horizon $T$,
--   $$\mathbb E[N_{a,T}]\le(1+\epsilon)\frac{\ln T+\ln\ln T}{K(\mu_a,\mu_1)}+C,$$
--   where $N_{a,T}$ is the number of draws of $a$ in rounds $1,\dots,T$ and $K(p,q)$ is the Bernoulli Kullback–Leibler divergence.
--
--   Since $\epsilon$ is arbitrary, the expected number of draws of every suboptimal arm grows at the Lai–Robbins rate $\ln T/K(\mu_a,\mu_1)$, which is the asymptotic optimality of Thompson Sampling.
--
--   **Formalization Note** The page's constant is $D(\epsilon,\mu_1,\mu_a)+N(b,\epsilon,\mu_1,\mu_a)+N_0(b)+5+2C_b$; it is a single constant $C$ here, chosen after the instance, the arm and $\epsilon$ and before $T$. For small $T$ the term $\ln\ln T$ is negative or Lean's junk value $\ln 0=0$; the constant absorbs these finitely many horizons. Lean arm $0$ is the paper's arm $1$. The hypotheses $0<\mu_a<1$ and $K\ge2$ are added.
-- source:
--   Kaufmann, Korda, Munos, Thompson Sampling: An Asymptotically Optimal Finite Time Analysis, arXiv:1205.4217v2, p. 4, Theorem 2 (proof §3.2, pp. 5–8)

import Mathlib
import Definitions.Def_KaufmannTS_Bernoulli_Model
open MeasureTheory ProbabilityTheory BanditAlgorithm AgrawalGoyalTS.TwoArmed
open scoped ENNReal

namespace KaufmannTS.Bernoulli

/-- Theorem 2, p. 4: for every `ε > 0` and every suboptimal arm `a` (Lean `a ≠ 0`; Lean arm `0` is the
paper's arm `1`) there is a constant `C` (the page's `D + N + N₀ + 5 + 2C_b`) such that for every
horizon `T`, `E[N_{a,T}] ≤ (1+ε)(ln T + ln ln T)/K(μ_a, μ₁) + C`. `tsPlays ω T a` counts the plays of
`a` in paper rounds `1, …, T`. -/
theorem theorem2_suboptimal_draws {K : ℕ} [NeZero K] (hK : 2 ≤ K) (μ : Fin K → ℝ)
    (hμ : ∀ a, μ a ∈ Set.Ioo (0 : ℝ) 1) (hopt : ∀ a, a ≠ 0 → μ a < μ 0)
    (a : Fin K) (ha : a ≠ 0) (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, ∀ T : ℕ,
      ∫⁻ ω, (tsPlays ω T a : ℝ≥0∞) ∂(tsLaw (bernoulliInstance μ hμ)) ≤
        ENNReal.ofReal ((1 + ε) * (Real.log T + Real.log (Real.log T)) /
          bernoulliRelativeEntropy (μ a) (μ 0) + C) := by sorry

end KaufmannTS.Bernoulli
