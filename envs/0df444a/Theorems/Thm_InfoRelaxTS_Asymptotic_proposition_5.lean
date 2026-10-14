-- Prove2me | Theorems.Thm_InfoRelaxTS_Asymptotic_proposition_5
-- name    : InfoRelaxTS.Asymptotic.proposition_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T01:22:19.978265+00:00
-- url     : https://prove2.me/theorems/f644b959-5b87-4ddc-a5e0-08be45ffc043
-- title:
--   Proposition 5, p. 54 — μ̂_{a,n} and the sample mean of arm a converge a.s. to μ_a(θ_a)
-- statement:
--   In the Bayesian bandit model with a conjugate prior family $\{\mathcal P_a(y_a)\}$ and a measurable Bayesian update $\mathcal U_a$, fix a belief vector $y$ and an arm $a$, and assume $\mathbb E_y|R_{a,n}| < \infty$. Let $\omega = (\theta, (R_{b,n})_{b,n}) \sim \mathcal I(y)$ be the outcome. Then, almost surely,
--   $$\lim_{n\to\infty} \hat\mu_{a,n}(\omega; y_a) = \lim_{n \to \infty} \frac1n \sum_{i=1}^n R_{a,i} = \mu_a(\theta_a).$$
--   Here $\hat\mu_{a,n}(\omega; y_a)$ is the posterior predictive mean of arm $a$ after its first $n$ rewards, and $\mu_a(\theta_a)$ is its conditional mean reward.
--
--   Both the Bayesian estimate and the frequentist estimate of an arm's mean are thus consistent. This is the fact that makes the IRS policies behave like Thompson sampling for long horizons (Proposition 1).
--
--   **Formalization Note.** The paper defines $\hat\mu_{a,n} = \mathbb E_{y_a}[\mu_a(\theta_a) \mid R_{a,1},\dots,R_{a,n}]$ (10). In the formalization, $\hat\mu_{a,n}(\omega; y_a) = \bar\mu_a(y_{a,n})$ is the predictive mean of the belief $y_{a,n}$ obtained by $n$ conjugate updates. Under conjugacy this is a version of the conditional expectation (10), so the statement is (108) for that version. The conjugacy hypothesis and the measurability of $\mathcal U_a$ belong to the model of §2.1. The integrability hypothesis is the page's $\mathbb E_y|R_{a,n}| < \infty$, stated for the first reward of arm $a$ under the belief $y_a$. Rewards are 0-based (the paper's $R_{a,i}$ is index $i-1$); at $n = 0$ the sample mean is $0/0 = 0$, which does not affect the limit.
-- source:
--   Min, Maglaras, Moallemi, Thompson Sampling with Information Relaxation Penalties, arXiv:1902.04251v2, p. 54, Proposition 5, (108)

import Mathlib
import Definitions.Def_InfoRelaxTS_Asymptotic_Setting

open MeasureTheory ProbabilityTheory Filter Topology

namespace InfoRelaxTS.Asymptotic

/-- Proposition 5 (p. 54): under the outcome law `ℐ(y)`, almost surely the posterior predictive
mean `μ̂_{a,n}` and the sample mean `(1/n) Σ_{i=1}^n R_{a,i}` of arm `a` both converge to the
conditional mean reward `μ_a(θ_a)`. -/
theorem proposition_5 {K : ℕ} {Θ Y : Type*} [MeasurableSpace Θ] [MeasurableSpace Y]
    (R : Fin K → Kernel Θ ℝ) [∀ a, IsMarkovKernel (R a)]
    (P : Fin K → Kernel Y Θ) [∀ a, IsMarkovKernel (P a)]
    (U : Fin K → Y → ℝ → Y) (hU : ∀ a, Measurable (Function.uncurry (U a)))
    (hconj : IsConjugate R P U) (y : Fin K → Y) (a : Fin K)
    (hint : Integrable (fun r : ℝ => r) ((R a) ∘ₘ (P a (y a)))) :
    ∀ᵐ ω ∂(I R P y),
      Tendsto (fun n => muHat R P U y a n ω) atTop (𝓝 (Monotone.mu R a (ω a).1)) ∧
      Tendsto (fun n : ℕ => (∑ i ∈ Finset.range n, (ω a).2 i) / (n : ℝ)) atTop
        (𝓝 (Monotone.mu R a (ω a).1)) := by sorry

end InfoRelaxTS.Asymptotic
