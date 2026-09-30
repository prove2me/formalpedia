-- Prove2me | Theorems.Thm_OptimalBAI_OptProportions_g_strictMono_bijective
-- name    : OptimalBAI.OptProportions.g_strictMono_bijective
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-28T01:59:40.644249+00:00
-- url     : https://prove2.me/theorems/0140433a-03a6-42b0-b608-6b7aad391de0
-- title:
--   §2.2 after eq. (4) — $g_a$ is a strictly increasing bijection of $[0,+\infty[$ onto $[0,d(\mu_1,\mu_a)[$
-- statement:
--   Let $\boldsymbol\mu$ be an exponential-family bandit model (every $\mu_a$ in the mean space $\dot b(\Theta)$) whose unique optimal arm is arm $1$. For every $a\in\{2,\dots,K\}$ let
--   $$g_a(x)=(1+x)\,I_{\frac1{1+x}}(\mu_1,\mu_a),\qquad x\ge0 .$$
--   Then $g_a$ is strictly increasing on $[0,+\infty[$ and maps $[0,+\infty[$ onto $[0,d(\mu_1,\mu_a)[$:
--   $$g_a\big([0,+\infty[\big)=[0,d(\mu_1,\mu_a)[ .$$
--
--   This is what makes the inverse $x_a=g_a^{-1}:[0,d(\mu_1,\mu_a)[\to[0,+\infty[$ well defined, the one-parameter reduction behind the formula for $w^*(\boldsymbol\mu)$ in Theorem 5.
--
--   **Formalization Note** Arm $1$ is index $0$ and $a$ ranges over the indices $\ne0$. "One-to-one mapping onto" is stated as strict monotonicity on $[0,+\infty[$ (hence injectivity) together with the equality of the image with $[0,d(\mu_1,\mu_a)[$. The paper's standing ordering is weakened to "arm 1 is the unique best arm".
-- source:
--   Garivier, Kaufmann, Optimal Best Arm Identification with Fixed Confidence, arXiv:1602.04589v2, p. 5, §2.2, claim after eq. (4) (proof: App. A.2, p. 17)

import Mathlib
import Definitions.Def_OptimalBAI_OptProportions_ExpFamily
import Definitions.Def_OptimalBAI_OptProportions_OptimalProportions

namespace OptimalBAI.OptProportions

/-- **§2.2, after eq. (4)** (Garivier–Kaufmann, arXiv:1602.04589v2, p. 5). For every arm
`a ∈ {2, …, K}` (index `a ≠ 0`), the function `g_a(x) = (1 + x) I_{1/(1+x)}(μ_1, μ_a)` is a
strictly increasing one-to-one mapping from `[0, +∞[` onto `[0, d(μ_1, μ_a)[`. -/
theorem g_strictMono_bijective {K : ℕ} [NeZero K] (F : ExpFamily) (μ : Fin K → ℝ)
    (hμ : ∀ a, μ a ∈ F.M) (hbest : IsBest μ 0) (a : Fin K) (ha : a ≠ 0) :
    StrictMonoOn (gFun F μ a) (Set.Ici 0) ∧
      gFun F μ a '' Set.Ici 0 = Set.Ico 0 (F.d (μ 0) (μ a)) := by sorry

end OptimalBAI.OptProportions
