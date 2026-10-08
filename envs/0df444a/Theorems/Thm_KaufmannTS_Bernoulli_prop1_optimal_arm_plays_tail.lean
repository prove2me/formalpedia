-- Prove2me | Theorems.Thm_KaufmannTS_Bernoulli_prop1_optimal_arm_plays_tail
-- name    : KaufmannTS.Bernoulli.prop1_optimal_arm_plays_tail
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T11:24:50.485182+00:00
-- url     : https://prove2.me/theorems/6a99cf5a-5f33-4154-8990-c9f275ff73ac
-- title:
--   Proposition 1, p. 4 — $\exists b\in(0,1)$: $\sum_t \mathbb P(N_{1,t} \le t^b) \le C_b < \infty$
-- statement:
--   Consider Thompson Sampling with uniform priors on a $K$-armed Bernoulli bandit ($K\ge2$) with means in $(0,1)$ and unique optimal arm $1$. Let $N_{1,t}$ be the number of draws of arm $1$ by the end of round $t$. There exist $b\in(0,1)$ and a finite constant $C_b$ such that
--   $$\sum_{t=1}^{\infty}\mathbb P\big(N_{1,t}\le t^b\big)\le C_b.$$
--
--   The optimal arm is therefore drawn at least $t^b$ times by round $t$ except on a family of events of summable probability. This is the central new ingredient of the analysis: it guarantees that the posterior of the optimal arm concentrates, which the standard index-policy argument requires.
--
--   **Formalization Note** The page writes $b=b(\mu_1,\mu_2)$ and $C_b=C_b(\mu_1,\mu_2)$; here $b$ and $C_b$ are chosen after the whole instance (the proof's $C_b$ in fact depends on $K$ and on all means through Step 8). The end of paper round $t$ is after Lean rounds $0,\dots,t-1$; Lean arm $0$ is the paper's arm $1$. The hypotheses $0<\mu_a<1$ and $K\ge2$ are added.
-- source:
--   Kaufmann, Korda, Munos, Thompson Sampling: An Asymptotically Optimal Finite Time Analysis, arXiv:1205.4217v2, p. 4, Proposition 1 (proof §3.3, pp. 8–11)

import Mathlib
import Definitions.Def_KaufmannTS_Bernoulli_Model
open MeasureTheory ProbabilityTheory BanditAlgorithm AgrawalGoyalTS.TwoArmed
open scoped ENNReal

namespace KaufmannTS.Bernoulli

/-- Proposition 1, p. 4: there are `b ∈ (0,1)` and `C_b < ∞` with `∑_{t≥1} P(N_{1,t} ≤ t^b) ≤ C_b`,
where `N_{1,t}` is the number of draws of the optimal arm by the end of paper round `t`. Paper round
`t = n + 1` ends after Lean rounds `0, …, n`, so `N_{1,t} = tsPlays ω (n+1) 0`. Lean arm `0` is the
paper's arm `1`. The constants are chosen after the whole instance. -/
theorem prop1_optimal_arm_plays_tail {K : ℕ} [NeZero K] (hK : 2 ≤ K) (μ : Fin K → ℝ)
    (hμ : ∀ a, μ a ∈ Set.Ioo (0 : ℝ) 1) (hopt : ∀ a, a ≠ 0 → μ a < μ 0) :
    ∃ b ∈ Set.Ioo (0 : ℝ) 1, ∃ Cb : ℝ,
      ∑' n : ℕ, tsLaw (bernoulliInstance μ hμ)
          {ω | (tsPlays ω (n + 1) 0 : ℝ) ≤ ((n : ℝ) + 1) ^ b} ≤ ENNReal.ofReal Cb := by sorry

end KaufmannTS.Bernoulli
