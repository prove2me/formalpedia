-- Prove2me | Theorems.Thm_KaufmannTS_Bernoulli_lemma4_saturated_sample_concentration
-- name    : KaufmannTS.Bernoulli.lemma4_saturated_sample_concentration
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T11:24:59.254118+00:00
-- url     : https://prove2.me/theorems/8876f9d0-61b6-4196-aaf6-d438d60ed28b
-- title:
--   Lemma 4, p. 9 — $\mathbb P(\exists s\le t, \exists a\ne 1: \theta_{a,s} > \mu_a+\delta_a, N_{a,s} > C_a\ln t) \le 2(K-1)/t^2$
-- statement:
--   Consider Thompson Sampling with uniform priors on a $K$-armed Bernoulli bandit ($K\ge2$) with means in $(0,1)$ and unique optimal arm $1$. For each suboptimal arm $a$ put $C_a=32/(\mu_1-\mu_a)^2$ and $\delta_a=(\mu_1-\mu_a)/2$. Then for every round $t\ge1$,
--   $$\mathbb P\big(\exists s\le t,\ \exists a\neq1:\ \theta_{a,s}>\mu_a+\delta_a,\ N_{a,s}>C_a\ln t\big)\le\frac{2(K-1)}{t^2}.$$
--
--   Once a suboptimal arm has been drawn about $C_a\ln t$ times, its posterior samples rarely overshoot its mean by more than half its gap; this is what keeps saturated arms from blocking the optimal arm in the proof of Proposition 1.
--
--   **Formalization Note** $N_{a,s}$ is the number of draws of $a$ before the sample $\theta_{a,s}$ is drawn; rounds $s=1,\dots,t$ are Lean rounds $0,\dots,t-1$, and Lean arm $0$ is the paper's arm $1$. The strict inequality $N_{a,s}>C_a\ln t$ is as printed (Definition 1 uses $\ge$). The paper does not prove the lemma; it states that it is easily adapted from Lemma 2 of Agrawal and Goyal. The hypotheses $0<\mu_a<1$ and $K\ge2$ are added.
-- source:
--   Kaufmann, Korda, Munos, Thompson Sampling: An Asymptotically Optimal Finite Time Analysis, arXiv:1205.4217v2, p. 9, Lemma 4 (C_a, δ_a from p. 8)

import Mathlib
import Definitions.Def_KaufmannTS_Bernoulli_Model
open MeasureTheory ProbabilityTheory BanditAlgorithm AgrawalGoyalTS.TwoArmed
open scoped ENNReal

namespace KaufmannTS.Bernoulli

/-- Lemma 4, p. 9: for every paper round `t ≥ 1`,
`P(∃ s ≤ t, ∃ a ≠ 1 : θ_{a,s} > μ_a + δ_a, N_{a,s} > C_a ln t) ≤ 2(K-1)/t²`, with
`C_a = 32/(μ₁-μ_a)²` and `δ_a = (μ₁-μ_a)/2`. Paper rounds `s = 1, …, t` are Lean rounds `s < t`;
`tsPlays ω s a` is `N_{a,s}` when `θ_{a,s}` is drawn; Lean arm `0` is the paper's arm `1`. -/
theorem lemma4_saturated_sample_concentration {K : ℕ} [NeZero K] (hK : 2 ≤ K) (μ : Fin K → ℝ)
    (hμ : ∀ a, μ a ∈ Set.Ioo (0 : ℝ) 1) (hopt : ∀ a, a ≠ 0 → μ a < μ 0)
    (t : ℕ) (ht : 1 ≤ t) :
    tsLaw (bernoulliInstance μ hμ)
        {ω | ∃ s < t, ∃ a : Fin K, a ≠ 0 ∧ μ a + satGap μ a < tsTheta ω s a ∧
          satConst μ a * Real.log t < (tsPlays ω s a : ℝ)} ≤
      ENNReal.ofReal (2 * ((K : ℝ) - 1) / (t : ℝ) ^ 2) := by sorry

end KaufmannTS.Bernoulli
