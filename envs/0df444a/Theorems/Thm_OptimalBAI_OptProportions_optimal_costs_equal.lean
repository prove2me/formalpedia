-- Prove2me | Theorems.Thm_OptimalBAI_OptProportions_optimal_costs_equal
-- name    : OptimalBAI.OptProportions.optimal_costs_equal
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-28T02:00:33.660921+00:00
-- url     : https://prove2.me/theorems/ca2f1b5e-3cae-4593-b231-0c574cc5d00f
-- title:
--   Lemma 4 — at the optimum, the costs $(w^*_1+w^*_a)I_{w^*_1/(w^*_1+w^*_a)}(\mu_1,\mu_a)$ are all equal
-- statement:
--   Let $\boldsymbol\mu=(\mu_1,\dots,\mu_K)$, $K\ge2$, be an exponential-family bandit model (every $\mu_a$ in the mean space $\dot b(\Theta)$) whose unique optimal arm is arm $1$, and let $w^*$ be an optimal proportion vector, i.e. any maximizer over $\Sigma_K$ of the transportation cost $w\mapsto\inf_{\boldsymbol\lambda\in\mathrm{Alt}(\boldsymbol\mu)}\sum_a w_a d(\mu_a,\lambda_a)$. Then for all $a,b\in\{2,\dots,K\}$,
--   $$(w^*_1+w^*_a)\,I_{\frac{w^*_1}{w^*_1+w^*_a}}(\mu_1,\mu_a)=(w^*_1+w^*_b)\,I_{\frac{w^*_1}{w^*_1+w^*_b}}(\mu_1,\mu_b).$$
--
--   Together with Lemma 3, this says that at the optimum every suboptimal arm is equally costly to promote, which reduces the $(K-1)$-dimensional maximization to a single real parameter.
--
--   **Formalization Note** Arm $1$ is index $0$ and $a,b$ range over the indices $\ne0$. The paper states the lemma for "the" $w^*(\boldsymbol\mu)$; it is stated here for every maximizer, as in the paper's proof ("Let $w^*$ be an element in argmax", App. A.2). The paper's standing ordering is weakened to "arm 1 is the unique best arm".
-- source:
--   Garivier, Kaufmann, Optimal Best Arm Identification with Fixed Confidence, arXiv:1602.04589v2, p. 5, Lemma 4 (proof: App. A.2, pp. 17-18)

import Mathlib
import Definitions.Def_OptimalBAI_OptProportions_ExpFamily
import Definitions.Def_OptimalBAI_OptProportions_OptimalProportions

namespace OptimalBAI.OptProportions

/-- **Lemma 4** (Garivier–Kaufmann, arXiv:1602.04589v2, p. 5). Let `μ` be an exponential-family
bandit model whose unique optimal arm is arm `1` (index `0`), and let `w*` be any optimal
proportion vector (any element of the argmax defining `w*(μ)`). For all `a, b ∈ {2, …, K}`
(indices `≠ 0`), `(w*_1 + w*_a) I_{w*_1/(w*_1+w*_a)}(μ_1, μ_a) = (w*_1 + w*_b) I_{w*_1/(w*_1+w*_b)}(μ_1, μ_b)`. -/
theorem optimal_costs_equal {K : ℕ} [NeZero K] (F : ExpFamily) (μ : Fin K → ℝ)
    (hK : 2 ≤ K) (hμ : ∀ a, μ a ∈ F.M) (hbest : IsBest μ 0)
    (w : Fin K → ℝ) (hw : IsOptimalProportion F μ w) (a b : Fin K) (ha : a ≠ 0) (hb : b ≠ 0) :
    (w 0 + w a) * jensenShannon F (w 0 / (w 0 + w a)) (μ 0) (μ a) =
      (w 0 + w b) * jensenShannon F (w 0 / (w 0 + w b)) (μ 0) (μ b) := by sorry

end OptimalBAI.OptProportions
