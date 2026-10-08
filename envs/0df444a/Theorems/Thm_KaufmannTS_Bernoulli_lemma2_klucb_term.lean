-- Prove2me | Theorems.Thm_KaufmannTS_Bernoulli_lemma2_klucb_term
-- name    : KaufmannTS.Bernoulli.lemma2_klucb_term
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T11:25:13.999237+00:00
-- url     : https://prove2.me/theorems/d44046e8-b53b-4276-a5e7-4cc11c3ba369
-- title:
--   Lemma 2, p. 6 — $(B) \le (1+\epsilon)(\ln T + \ln\ln T)/K(\mu_a,\mu_1) + D$ for $T > N$
-- statement:
--   Consider Thompson Sampling with uniform priors on a $K$-armed Bernoulli bandit ($K\ge2$) with means in $(0,1)$ and unique optimal arm $1$. Let $a\neq1$ and $\epsilon>0$. There exist constants $N$ and $D>0$ such that for every horizon $T>N$,
--   $$B_T=\sum_{t=1}^{T}\mathbb P\Big(u_{a,t}>\mu_1-\sqrt{\tfrac{6\ln t}{N_{1,t}}},\ A_t=a\Big)\le(1+\epsilon)\frac{\ln T+\ln\ln T}{K(\mu_a,\mu_1)}+D,$$
--   where $u_{a,t}$ is the KL-UCB index with horizon $T$ and $K(p,q)$ is the Bernoulli Kullback–Leibler divergence.
--
--   This lemma produces the leading term $(1+\epsilon)\ln T/K(\mu_a,\mu_1)$ of the Lai–Robbins rate in the regret bound.
--
--   **Formalization Note** The page writes the constants as $N(b,\epsilon,\mu_1,\mu_a)$ and $D(\epsilon,\mu_1,\mu_a)$; here both are chosen after the whole instance and $\epsilon$. Two printed slips make the finer dependence unusable: the explicit $D$ printed at the end of the proof (p. 7) is smaller than the sum it is claimed to bound, and the proof drops the term $C_b$ of its first display, which depends on $\mu_2$ and $K$. Lean arm $0$ is the paper's arm $1$; Lean round $t$ is the paper's round $t+1$. The hypotheses $0<\mu_a<1$ and $K\ge2$ are added.
-- source:
--   Kaufmann, Korda, Munos, Thompson Sampling: An Asymptotically Optimal Finite Time Analysis, arXiv:1205.4217v2, p. 6, Lemma 2 (proof pp. 6–7)

import Mathlib
import Definitions.Def_KaufmannTS_Bernoulli_Model
open MeasureTheory ProbabilityTheory BanditAlgorithm AgrawalGoyalTS.TwoArmed
open scoped ENNReal

namespace KaufmannTS.Bernoulli

/-- Lemma 2, p. 6: for every suboptimal arm `a` (Lean `a ≠ 0`; Lean arm `0` is the paper's arm `1`)
and every `ε > 0` there are constants `N` and `D > 0` such that for all `T > N`,
`B ≤ (1+ε)(ln T + ln ln T)/K(μ_a, μ₁) + D`, where `B = termB μ hμ a T` is term `B` of (4). The
constants may depend on the whole instance (`K`, `μ`) and on `ε`. -/
theorem lemma2_klucb_term {K : ℕ} [NeZero K] (hK : 2 ≤ K) (μ : Fin K → ℝ)
    (hμ : ∀ a, μ a ∈ Set.Ioo (0 : ℝ) 1) (hopt : ∀ a, a ≠ 0 → μ a < μ 0)
    (a : Fin K) (ha : a ≠ 0) (ε : ℝ) (hε : 0 < ε) :
    ∃ N D : ℝ, 0 < D ∧ ∀ T : ℕ, N < T →
      termB μ hμ a T ≤
        ENNReal.ofReal ((1 + ε) * (Real.log T + Real.log (Real.log T)) /
          bernoulliRelativeEntropy (μ a) (μ 0) + D) := by sorry

end KaufmannTS.Bernoulli
