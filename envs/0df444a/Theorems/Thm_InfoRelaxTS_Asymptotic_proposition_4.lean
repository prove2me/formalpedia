-- Prove2me | Theorems.Thm_InfoRelaxTS_Asymptotic_proposition_4
-- name    : InfoRelaxTS.Asymptotic.proposition_4
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-14T01:22:15.011107+00:00
-- url     : https://prove2.me/theorems/5d793dfa-921c-467c-984a-9b1ff23d2c69
-- title:
--   Proposition 4, p. 53 — μ_a(θ_a) and max_a μ_a(θ_a) are integrable, so W^TS(T, y) < ∞
-- statement:
--   In the Bayesian bandit model, fix a belief vector $y = (y_1,\dots,y_K)$ and assume the rewards are integrable under it: $\mathbb E_y|R_{a,n}| < \infty$ for every arm $a$. Then, for every arm $a$, the conditional mean reward $\mu_a(\theta_a)$ is integrable under the prior $\mathcal P_a(y_a)$, and the best conditional mean is integrable under the joint prior $\mathcal P(y) = \bigotimes_a \mathcal P_a(y_a)$:
--   $$\mathbb E_y|\mu_a(\theta_a)| < \infty \quad \forall a \in \mathcal A, \qquad \mathbb E_y\Big|\max_{a \in \mathcal A} \mu_a(\theta_a)\Big| < \infty.$$
--   Equivalently, the Thompson sampling performance bound $W^{TS}(T, y) = T \times \mathbb E_y[\max_a \mu_a(\theta_a)]$ is finite for every $T \in \mathbb N$.
--
--   This is the regularity step behind Proposition 5. It shows that $\mu_a(\theta_a)$ is an $L^1$ random variable, so that its posterior means form a uniformly integrable martingale.
--
--   **Formalization Note.** "$< \infty$" for a real expectation is read as integrability (Lean's Bochner integral is finite by definition). Since the rewards of an arm are i.i.d. given $\theta_a$, the hypothesis is stated for the first reward, whose law is $\mathcal R_a$ averaged over $\mathcal P_a(y_a)$. Arms are `Fin K` with $K \ge 1$ (`NeZero K`), so that the maximum over arms is defined.
-- source:
--   Min, Maglaras, Moallemi, Thompson Sampling with Information Relaxation Penalties, arXiv:1902.04251v2, p. 53, Proposition 4, (105)

import Mathlib
import Definitions.Def_InfoRelaxTS_Asymptotic_Setting

open MeasureTheory ProbabilityTheory Filter Topology

namespace InfoRelaxTS.Asymptotic

/-- Proposition 4 (p. 53): if the rewards are integrable under the belief `y`, then each
`μ_a(θ_a)` is integrable under the prior `𝒫_a(y_a)`, and so is `max_a μ_a(θ_a)` under `𝒫(y)`
(i.e. `W^TS(T, y) = T · 𝔼_y[max_a μ_a(θ_a)] < ∞` for every `T`). -/
theorem proposition_4 {K : ℕ} [NeZero K] {Θ Y : Type*} [MeasurableSpace Θ] [MeasurableSpace Y]
    (R : Fin K → Kernel Θ ℝ) [∀ a, IsMarkovKernel (R a)]
    (P : Fin K → Kernel Y Θ) [∀ a, IsMarkovKernel (P a)] (y : Fin K → Y)
    (hint : ∀ a, Integrable (fun r : ℝ => r) ((R a) ∘ₘ (P a (y a)))) :
    (∀ a, Integrable (fun θ => Monotone.mu R a θ) (P a (y a))) ∧
      Integrable (fun θ : Fin K → Θ => Finset.univ.sup' Finset.univ_nonempty fun a => Monotone.mu R a (θ a))
        (priorLaw P y) := by sorry

end InfoRelaxTS.Asymptotic
