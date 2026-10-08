-- Prove2me | Theorems.Thm_KaufmannTS_Bernoulli_lemma1_underestimation_sum
-- name    : KaufmannTS.Bernoulli.lemma1_underestimation_sum
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T11:25:20.832674+00:00
-- url     : https://prove2.me/theorems/e1889d3f-fe49-484a-9127-94328dc59b0d
-- title:
--   Lemma 1, p. 5 — $\sum_t \mathbb P(\theta_{1,t} \le \mu_1 - \sqrt{6\ln t/N_{1,t}}) \le N_0(b) + 3 + C_b$
-- statement:
--   Consider Thompson Sampling with uniform priors on a $K$-armed Bernoulli bandit ($K\ge2$) with means in $(0,1)$ and unique optimal arm $1$. Let $b\in(0,1)$, and let $N_0=N_0(b)$ be a natural number such that
--   $$\sqrt{6t^b\ln t}-1>\sqrt{5t^b\ln t}\qquad\text{for every integer }t\ge N_0.$$
--   Then
--   $$\sum_{t=1}^{\infty}\mathbb P\Big(\theta_{1,t}\le\mu_1-\sqrt{\tfrac{6\ln t}{N_{1,t}}}\Big)\le N_0+3+C_b,\qquad C_b=\sum_{t=1}^{\infty}\mathbb P\big(N_{1,t}\le t^b\big),$$
--   with the convention $\sqrt{6\ln t/0}=\infty$.
--
--   The lemma shows that the under-estimation term $A$ of display (4) stays bounded as $T\to\infty$ once Proposition 1 makes $C_b$ finite.
--
--   **Formalization Note** $N_0(b)$ is the constant defined in the proof (p. 6); it is a hypothesis here, and such an $N_0$ exists for every $b\in(0,1)$. In $C_b$ the count $N_{1,t}$ is the one in the event, the number of draws of arm $1$ before the sample $\theta_{1,t}$ is drawn, which is the count the proof splits on; Proposition 1's sum uses the count at the end of round $t$, which is larger by at most one round. Lean arm $0$ is the paper's arm $1$; Lean round $t$ is the paper's round $t+1$. The hypotheses $0<\mu_a<1$ and $K\ge2$ are added.
-- source:
--   Kaufmann, Korda, Munos, Thompson Sampling: An Asymptotically Optimal Finite Time Analysis, arXiv:1205.4217v2, p. 5, Lemma 1 (N₀(b) defined in its proof, p. 6)

import Mathlib
import Definitions.Def_KaufmannTS_Bernoulli_Model
open MeasureTheory ProbabilityTheory BanditAlgorithm AgrawalGoyalTS.TwoArmed
open scoped ENNReal

namespace KaufmannTS.Bernoulli

/-- Lemma 1, p. 5, with the constant `N₀(b)` of its proof (p. 6): let `b ∈ (0,1)` and let `N₀` be such
that `√(6 t^b ln t) - 1 > √(5 t^b ln t)` for every `t ≥ N₀`. Then
`∑_{t≥1} P(θ_{1,t} ≤ μ₁ - √(6 ln t / N_{1,t})) ≤ N₀ + 3 + C_b`, where `C_b = ∑_{t≥1} P(N_{1,t} ≤ t^b)`
is the sum of Proposition 1 read with the same count `N_{1,t}` as the event (the count when `θ_{1,t}`
is drawn). Lean round `t` is paper round `t + 1`; Lean arm `0` is the paper's arm `1`. -/
theorem lemma1_underestimation_sum {K : ℕ} [NeZero K] (hK : 2 ≤ K) (μ : Fin K → ℝ)
    (hμ : ∀ a, μ a ∈ Set.Ioo (0 : ℝ) 1) (hopt : ∀ a, a ≠ 0 → μ a < μ 0)
    (b : ℝ) (hb : b ∈ Set.Ioo (0 : ℝ) 1) (N₀ : ℕ)
    (hN₀ : ∀ t : ℕ, N₀ ≤ t →
      Real.sqrt (5 * (t : ℝ) ^ b * Real.log t) < Real.sqrt (6 * (t : ℝ) ^ b * Real.log t) - 1) :
    ∑' t : ℕ, tsLaw (bernoulliInstance μ hμ) (underEstEvent μ t) ≤
      (N₀ : ℝ≥0∞) + 3 +
        ∑' t : ℕ, tsLaw (bernoulliInstance μ hμ)
          {ω | (tsPlays ω t 0 : ℝ) ≤ ((t : ℝ) + 1) ^ b} := by sorry

end KaufmannTS.Bernoulli
