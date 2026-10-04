-- Prove2me | Theorems.Thm_OptimalBAI_OptProportions_transport_cost_eq_min
-- name    : OptimalBAI.OptProportions.transport_cost_eq_min
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-28T01:59:12.507843+00:00
-- url     : https://prove2.me/theorems/ba9a0537-4495-4e83-bfe0-c7d068ce4bf4
-- title:
--   Lemma 3 — the transportation cost is $\min_{a\ne1}(w_1+w_a)I_{w_1/(w_1+w_a)}(\mu_1,\mu_a)$
-- statement:
--   Let $\boldsymbol\mu=(\mu_1,\dots,\mu_K)$, $K\ge2$, be an exponential-family bandit model (every $\mu_a$ in the mean space $\dot b(\Theta)$) whose unique optimal arm is arm $1$: $\mu_1>\mu_a$ for all $a\ne1$. Then for every $w\in\Sigma_K$,
--   $$\inf_{\boldsymbol\lambda\in\mathrm{Alt}(\boldsymbol\mu)}\left(\sum_{a=1}^K w_a d(\mu_a,\lambda_a)\right)=\min_{a\ne1}\,(w_1+w_a)\,I_{\frac{w_1}{w_1+w_a}}(\mu_1,\mu_a),$$
--   where $I_\alpha$ is the parameterized Jensen–Shannon divergence of eq. (3). In words: the cheapest way to make a suboptimal arm $a$ look best is to move $\mu_1$ and $\mu_a$ to a common weighted mean, and the transportation cost is the smallest of these $K-1$ costs.
--
--   Lemma 3 turns the inner infimum of the characteristic time $T^*(\boldsymbol\mu)^{-1}$ into a finite minimum of explicit one-dimensional quantities, which is the starting point of the computation of the optimal proportions $w^*(\boldsymbol\mu)$.
--
--   **Formalization Note** Arm $1$ is index $0$. The minimum is stated as the existence of an arm $a\ne 1$ whose term is no larger than every other term and equals the infimum. The infimum is taken in the extended reals over the paper's $\mathrm{Alt}(\boldsymbol\mu)\subseteq\mathcal S$. When $w_1=w_a=0$ the subscript $w_1/(w_1+w_a)$ is $0/0$, which Lean evaluates as $0$; the term is then $0\cdot I_0=0$, the value it has under any convention. The paper states the lemma under its standing ordering $\mu_1>\mu_2\ge\dots\ge\mu_K$; only "arm 1 is the unique best arm" is assumed here, which is weaker.
-- source:
--   Garivier, Kaufmann, Optimal Best Arm Identification with Fixed Confidence, arXiv:1602.04589v2, p. 5, Lemma 3 (proof: App. A.1, p. 17)

import Mathlib
import Definitions.Def_OptimalBAI_OptProportions_ExpFamily
import Definitions.Def_OptimalBAI_OptProportions_OptimalProportions

namespace OptimalBAI.OptProportions

/-- **Lemma 3** (Garivier–Kaufmann, arXiv:1602.04589v2, p. 5). Let `μ` be an exponential-family
bandit model whose unique optimal arm is arm `1` (index `0`). For every `w ∈ Σ_K`,
`inf_{λ ∈ Alt(μ)} ∑_a w_a d(μ_a, λ_a) = min_{a ≠ 1} (w_1 + w_a) I_{w_1/(w_1+w_a)}(μ_1, μ_a)`.
The minimum is stated as an arm `a ≠ 0` whose term is smallest and equals the infimum. -/
theorem transport_cost_eq_min {K : ℕ} [NeZero K] (F : ExpFamily) (μ : Fin K → ℝ)
    (hK : 2 ≤ K) (hμ : ∀ a, μ a ∈ F.M) (hbest : IsBest μ 0)
    (w : Fin K → ℝ) (hw : w ∈ simplex K) :
    ∃ a : Fin K, a ≠ 0 ∧
      (∀ b : Fin K, b ≠ 0 →
        (w 0 + w a) * jensenShannon F (w 0 / (w 0 + w a)) (μ 0) (μ a) ≤
          (w 0 + w b) * jensenShannon F (w 0 / (w 0 + w b)) (μ 0) (μ b)) ∧
      transportCost F μ w =
        (((w 0 + w a) * jensenShannon F (w 0 / (w 0 + w a)) (μ 0) (μ a) : ℝ) : EReal) := by sorry

end OptimalBAI.OptProportions
