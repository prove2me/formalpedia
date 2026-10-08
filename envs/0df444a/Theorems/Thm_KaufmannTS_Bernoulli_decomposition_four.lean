-- Prove2me | Theorems.Thm_KaufmannTS_Bernoulli_decomposition_four
-- name    : KaufmannTS.Bernoulli.decomposition_four
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T11:24:47.571047+00:00
-- url     : https://prove2.me/theorems/d532a34e-f8fe-44d5-82d4-35a33335dd1d
-- title:
--   §3.2 Step 1, p. 5, display (4) — $\mathbb E[N_{a,T}] \le A + B + 2$
-- statement:
--   Consider Thompson Sampling with uniform priors on a $K$-armed Bernoulli bandit ($K\ge2$) whose means lie in $(0,1)$ and whose arm $1$ is the unique optimal arm. Let $a\neq1$ be a suboptimal arm and $T\ge3$ a horizon. Then the expected number of draws of $a$ in rounds $1,\dots,T$ satisfies
--   $$\mathbb E[N_{a,T}]\le\underbrace{\sum_{t=1}^{T}\mathbb P\Big(\theta_{1,t}\le\mu_1-\sqrt{\tfrac{6\ln t}{N_{1,t}}}\Big)}_{A}+\underbrace{\sum_{t=1}^{T}\mathbb P\Big(u_{a,t}>\mu_1-\sqrt{\tfrac{6\ln t}{N_{1,t}}},\ A_t=a\Big)}_{B}+2,$$
--   where $u_{a,t}$ is the KL-UCB index of arm $a$ at round $t$ with horizon $T$, and $\sqrt{6\ln t/0}=\infty$.
--
--   This splits the draws of a suboptimal arm into an under-estimation term for the optimal arm and a KL-UCB-type term, the two quantities bounded by Lemmas 1 and 2.
--
--   **Formalization Note** The page writes $\mathbb E[N_{a,t}]$ for $\mathbb E[N_{a,T}]$ (a typo) and "$T\ge e$"; for integer horizons this is $T\ge3$. Lean arm $0$ is the paper's arm $1$; Lean round $t$ is the paper's round $t+1$. The hypotheses $0<\mu_a<1$ and $K\ge2$ are added (the paper assumes them implicitly); unique optimality of arm $1$ is the standing assumption of §2.
-- source:
--   Kaufmann, Korda, Munos, Thompson Sampling: An Asymptotically Optimal Finite Time Analysis, arXiv:1205.4217v2, p. 5, §3.2 Step 1, display (4)

import Mathlib
import Definitions.Def_KaufmannTS_Bernoulli_Model
open MeasureTheory ProbabilityTheory BanditAlgorithm AgrawalGoyalTS.TwoArmed
open scoped ENNReal

namespace KaufmannTS.Bernoulli

/-- Display (4), §3.2 Step 1, p. 5: for every suboptimal arm `a` (Lean arm `a ≠ 0`; Lean arm `0` is
the paper's arm `1`) and every horizon `T ≥ 3` (the page's `T ≥ e`),
`E[N_{a,T}] ≤ A + B + 2`. `tsPlays ω T a` counts the plays of `a` in paper rounds `1, …, T`
(Lean rounds `0, …, T-1`); `termA`, `termB` are the sums `A`, `B` of (4). -/
theorem decomposition_four {K : ℕ} [NeZero K] (hK : 2 ≤ K) (μ : Fin K → ℝ)
    (hμ : ∀ a, μ a ∈ Set.Ioo (0 : ℝ) 1) (hopt : ∀ a, a ≠ 0 → μ a < μ 0)
    (a : Fin K) (ha : a ≠ 0) (T : ℕ) (hT : 3 ≤ T) :
    ∫⁻ ω, (tsPlays ω T a : ℝ≥0∞) ∂(tsLaw (bernoulliInstance μ hμ)) ≤
      termA μ hμ T + termB μ hμ a T + 2 := by sorry

end KaufmannTS.Bernoulli
