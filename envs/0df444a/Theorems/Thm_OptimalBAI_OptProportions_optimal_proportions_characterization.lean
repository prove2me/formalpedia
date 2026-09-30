-- Prove2me | Theorems.Thm_OptimalBAI_OptProportions_optimal_proportions_characterization
-- name    : OptimalBAI.OptProportions.optimal_proportions_characterization
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-28T02:01:06.3758+00:00
-- url     : https://prove2.me/theorems/85f7392c-cf6b-440a-91cd-b3c96c240ac3
-- title:
--   Theorem 5 — the optimal proportions $w^*(\boldsymbol\mu)$ are $x_a(y^*)/\sum_i x_i(y^*)$ with $F_{\boldsymbol\mu}(y^*)=1$
-- statement:
--   Let $\boldsymbol\mu=(\mu_1,\dots,\mu_K)$, $K\ge2$, be an exponential-family bandit model (every $\mu_a$ in the mean space $\dot b(\Theta)$) with sorted means
--   $$\mu_1>\mu_2\ge\dots\ge\mu_K ,$$
--   and write $D=d(\mu_1,\mu_2)$. Let $x_a=g_a^{-1}$ be the inverse functions of Section 2.2 ($x_1\equiv1$) and
--   $$F_{\boldsymbol\mu}(y)=\sum_{a=2}^K\frac{d\Big(\mu_1,\frac{\mu_1+x_a(y)\mu_a}{1+x_a(y)}\Big)}{d\Big(\mu_a,\frac{\mu_1+x_a(y)\mu_a}{1+x_a(y)}\Big)} .$$
--   Then:
--
--   1. $F_{\boldsymbol\mu}$ is continuous and strictly increasing on $[0,D[$, $F_{\boldsymbol\mu}(0)=0$, and $F_{\boldsymbol\mu}(y)\to+\infty$ as $y\to D$ from below;
--   2. the equation $F_{\boldsymbol\mu}(y)=1$ has a unique solution $y^*\in[0,D[$;
--   3. a vector $w$ is an optimal proportion vector (a maximizer over $\Sigma_K$ of $w\mapsto\inf_{\boldsymbol\lambda\in\mathrm{Alt}(\boldsymbol\mu)}\sum_a w_ad(\mu_a,\lambda_a)$) if and only if, for every arm $a$,
--   $$w_a=\frac{x_a(y^*)}{\sum_{i=1}^K x_i(y^*)} .$$
--
--   In particular the maximizer $w^*(\boldsymbol\mu)$ in the definition of the characteristic time exists, is unique, and is computed by solving one scalar equation. This is the formula used by the Track-and-Stop strategy to compute the proportions it tracks.
--
--   **Formalization Note** Arm $1$ is index $0$ and arm $2$ is index $1$. The paper says "increasing"; its proof (App. A.2) shows "strictly increasing", which is what the uniqueness of $y^*$ uses, and that is what is stated. The paper's "$w^*_a(\boldsymbol\mu)=\dots$" presupposes that the argmax exists and is a single point; clause 3 states exactly this, as an equivalence for every $w$. The sum in the denominator is written with a separate index. $x_a$ is only evaluated on $[0,D[\subseteq[0,d(\mu_1,\mu_a)[$ (by the ordering), where it is the true inverse of $g_a$.
-- source:
--   Garivier, Kaufmann, Optimal Best Arm Identification with Fixed Confidence, arXiv:1602.04589v2, p. 5, Theorem 5, eqs. (5)-(6) (proof: App. A.2, pp. 17-18)

import Mathlib
import Definitions.Def_OptimalBAI_OptProportions_ExpFamily
import Definitions.Def_OptimalBAI_OptProportions_OptimalProportions

namespace OptimalBAI.OptProportions

/-- **Theorem 5** (Garivier–Kaufmann, arXiv:1602.04589v2, p. 5). Let `μ` be an exponential-family
bandit model with `K ≥ 2` arms, sorted as `μ_1 > μ_2 ≥ ⋯ ≥ μ_K` (0-based: `μ 0 > μ 1 ≥ ⋯`), and
`D = d(μ_1, μ_2)`. Then `F_μ` of eq. (6) is continuous and strictly increasing on `[0, D[`,
`F_μ(0) = 0`, `F_μ(y) → ∞` as `y → D⁻`; the equation `F_μ(y) = 1` has a unique solution `y*`
in `[0, D[`; and the optimal proportion vectors `w*(μ)` are exactly the vector
`w*_a = x_a(y*) / ∑_{i} x_i(y*)` of eq. (5) (so the argmax exists and is unique). -/
theorem optimal_proportions_characterization {K : ℕ} [NeZero K] (F : ExpFamily)
    (μ : Fin K → ℝ) (hK : 2 ≤ K) (hμ : ∀ a, μ a ∈ F.M) (hμ0 : μ 1 < μ 0)
    (hsorted : ∀ a b : Fin K, 1 ≤ a → a ≤ b → μ b ≤ μ a) :
    ContinuousOn (FFun F μ) (Set.Ico 0 (F.d (μ 0) (μ 1))) ∧
      StrictMonoOn (FFun F μ) (Set.Ico 0 (F.d (μ 0) (μ 1))) ∧
      FFun F μ 0 = 0 ∧
      Filter.Tendsto (FFun F μ)
        (nhdsWithin (F.d (μ 0) (μ 1)) (Set.Iio (F.d (μ 0) (μ 1)))) Filter.atTop ∧
      ∃ ystar : ℝ, ystar ∈ Set.Ico 0 (F.d (μ 0) (μ 1)) ∧ FFun F μ ystar = 1 ∧
        (∀ y ∈ Set.Ico 0 (F.d (μ 0) (μ 1)), FFun F μ y = 1 → y = ystar) ∧
        ∀ w : Fin K → ℝ, IsOptimalProportion F μ w ↔
          ∀ a, w a = xFun F μ a ystar / ∑ i, xFun F μ i ystar := by sorry

end OptimalBAI.OptProportions
