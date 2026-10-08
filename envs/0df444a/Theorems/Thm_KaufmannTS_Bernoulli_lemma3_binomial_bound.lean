-- Prove2me | Theorems.Thm_KaufmannTS_Bernoulli_lemma3_binomial_bound
-- name    : KaufmannTS.Bernoulli.lemma3_binomial_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T11:24:36.354513+00:00
-- url     : https://prove2.me/theorems/d5dffbde-8c87-4292-ba0e-13ab3302f2c8
-- title:
--   §3.4, pp. 11–13 — the binomial bound that proves Lemma 3 (p. 9)
-- statement:
--   Let $0<\mu_2<\mu_1<1$, $\delta=(\mu_1-\mu_2)/2$ and $y=\mu_2+\delta$. Write $f^B_{j,p}$ and $F^B_{j,p}$ for the probability mass function and the cumulative distribution function of the binomial distribution with $j$ trials and success probability $p$. With the constants $\alpha=\alpha_{\mu_1,\mu_2}$, $\lambda_0=\lambda_0(\mu_1,\mu_2)$, $d_{\lambda,\mu_1,\mu_2}$ and $C_{\lambda,\mu_1,\mu_2}$ of Lemma 3:
--
--   1. $\lambda_0>1$;
--   2. for every $\lambda\in(1,\lambda_0)$, $C_{\lambda,\mu_1,\mu_2}>0$ and $d_{\lambda,\mu_1,\mu_2}>0$;
--   3. for every such $\lambda$, every integer $j\ge0$ and every real $f>0$,
--   $$\sum_{s=0}^{j}\big(1-F^B_{j+1,y}(s)\big)^{f}f^B_{j,\mu_1}(s)\le\alpha^{f}+C_{\lambda,\mu_1,\mu_2}\,\frac{1}{f^{\lambda}}\,e^{-j\,d_{\lambda,\mu_1,\mu_2}}.$$
--
--   The left side is the probability that $f$ conditionally independent posterior samples $\mathrm{Beta}(S+1,j-S+1)$ of the optimal arm, with $S\sim\mathrm{Bin}(j,\mu_1)$ successes after $j$ draws, all stay below $\mu_2+\delta$. Lemma 3 of the paper is this bound applied, through the Beta–Binomial identity, to a stretch of rounds of length $f$ during which the optimal arm is not drawn.
--
--   **Formalization Note** Lemma 3 is printed for "every (random) interval $\mathcal J$ included in $\mathcal I_j$". Its proof (p. 11) treats the samples on $\mathcal J$ as i.i.d. given $S_{1,\tau_j}$, which is justified when $\mathcal J$ is chosen without looking at those samples but not for an arbitrary random interval; the mission therefore states the analytic core of §3.4, to which the proof reduces the lemma. The constant $C_{\lambda,\mu_1,\mu_2}$ is the sign-corrected one (see the Lemma3Constants definition). The paper asserts without proof that $\lambda_2\le\lambda_1$ on p. 13; the statement uses $\lambda_0$ in the printed closed form. $\mu_2$ is a free parameter in $(0,\mu_1)$ rather than the second-best mean of a bandit.
-- source:
--   Kaufmann, Korda, Munos, Thompson Sampling: An Asymptotically Optimal Finite Time Analysis, arXiv:1205.4217v2, p. 9, Lemma 3; §3.4, pp. 11–13

import Mathlib
import Definitions.Def_AgrawalGoyalTS_TwoArmed_BetaBinomial
import Definitions.Def_KaufmannTS_Bernoulli_Lemma3Constants
open AgrawalGoyalTS.TwoArmed

namespace KaufmannTS.Bernoulli

/-- §3.4, pp. 11–13, the bound that proves Lemma 3 (p. 9). Let `0 < μ₂ < μ₁ < 1`, `δ = (μ₁-μ₂)/2`,
`y = μ₂ + δ`. Then `λ₀ = λ₀(μ₁,μ₂) > 1`, and for every `λ ∈ (1, λ₀)` the constants
`C_{λ,μ₁,μ₂}`, `d_{λ,μ₁,μ₂}` are positive and, for every `j ∈ ℕ` and every real `f > 0`,
`∑_{s=0}^{j} (1 - F^B_{j+1,y}(s))^f f^B_{j,μ₁}(s) ≤ α^f + C_{λ,μ₁,μ₂} f^{-λ} e^{-j d_{λ,μ₁,μ₂}}`,
with `α = (1/2)^{1-y}`. `C_{λ,μ₁,μ₂}` is the sign-corrected constant `lemma3C`. -/
theorem lemma3_binomial_bound (μ₁ μ₂ : ℝ) (hμ₂ : 0 < μ₂) (h12 : μ₂ < μ₁) (hμ₁ : μ₁ < 1) :
    1 < lemma3Lambda0 μ₁ μ₂ ∧
      ∀ lam : ℝ, 1 < lam → lam < lemma3Lambda0 μ₁ μ₂ →
        0 < lemma3C lam μ₁ μ₂ ∧ 0 < lemma3D lam μ₁ μ₂ ∧
        ∀ (j : ℕ) (f : ℝ), 0 < f →
          ∑ s ∈ Finset.range (j + 1),
              (1 - binomCDF (j + 1) (lemma3Y μ₁ μ₂) (s : ℝ)) ^ f * binomPMF j μ₁ s ≤
            lemma3Alpha μ₁ μ₂ ^ f +
              lemma3C lam μ₁ μ₂ * f ^ (-lam) * Real.exp (-(j : ℝ) * lemma3D lam μ₁ μ₂) := by sorry

end KaufmannTS.Bernoulli
