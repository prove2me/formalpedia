-- Prove2me | Theorems.Thm_KLTNuclear_Lasso_theorem_2_lasso
-- name    : KLTNuclear.Lasso.theorem_2_lasso
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T07:52:20.497137+00:00
-- url     : https://prove2.me/theorems/f852ed94-9199-4133-8afe-955272c7fd6f
-- title:
--   Theorem 2, p. 11 — (2.19) for diagonal matrices: if λ ≥ 3‖M‖∞ the Lasso obeys a sharp sparsity oracle inequality
-- statement:
--   Let $x_1,\dots,x_n\in\mathbb R^p$ be a fixed design, $n\ge1$, $\beta^*\in\mathbb R^p$, $\xi\in\mathbb R^n$ and $Y_i = x_i^\top\beta^*+\xi_i$. Let $\lambda>0$ satisfy $\lambda \ge 3\|\mathbf M\|_\infty$ with $\mathbf M = \frac1n\sum_{i=1}^n\xi_ix_i$, and let $\hat\beta^\lambda$ be any Lasso estimator,
--   $$
--   \hat\beta^\lambda \in \arg\min_{\beta\in\mathbb R^p}\Big\{\frac1n\sum_{i=1}^n(Y_i-x_i^\top\beta)^2+\lambda|\beta|_1\Big\}.
--   $$
--   Then
--   $$
--   \frac1n|\mathbb X(\hat\beta^\lambda-\beta^*)|_2^2 \le \inf_{\beta\in\mathbb R^p}\Big[\frac1n|\mathbb X(\beta-\beta^*)|_2^2 + \lambda^2\mu^2(\beta)M(\beta)\Big],
--   $$
--   where $\mu(\beta) = \mu_5(\beta)$ is the restricted constant at the support of $\beta$ and $M(\beta)$ the number of its nonzero components.
--
--   This is the deterministic sparsity oracle inequality behind Theorem 14. Its leading constant is $1$, which is what "sharp" means here.
--
--   **Formalization Note** This is Theorem 2 of the paper for $\mathbb A$ the diagonal $p\times p$ matrices and non-random diagonal $X_i$, written in vector form as the paper does on pp. 24–26: $\|\operatorname{diag}\beta\|_{L_2(\Pi)}^2 = \frac1n|\mathbb X\beta|_2^2$, $\operatorname{rank}(\operatorname{diag}\beta) = M(\beta)$, $\|\mathbf M\|_\infty$ is the sup norm of the vector $\mathbf M$, and $L_n(\operatorname{diag}\beta)$ differs from the Lasso criterion by the constant $\frac1n\sum_iY_i^2$. The infimum over $\beta$ is stated as "for every $\beta$", and $\mu(\beta)$ enters through every witness $\mu'$ (see the definition), which is equivalent to using the infimum. $\|\mathbf M\|_\infty\le\lambda/3$ is written coordinatewise; $\lambda>0$ is the standing assumption of (1.6).
-- source:
--   Koltchinskii, Lounici, Tsybakov, Nuclear-Norm Penalization and Optimal Rates for Noisy Low-Rank Matrix Completion, arXiv:1011.6256v4, p. 11, Theorem 2, (2.19); diagonal case: Example 4 (p. 3), remark after Theorem 2 (pp. 11–12), §5.4 (pp. 24–26)

import Mathlib
import Definitions.Def_KLTNuclear_Lasso_Model

namespace KLTNuclear.Lasso

/-- Theorem 2, (2.19), arXiv:1011.6256v4, p. 11, for `𝔸` the space of diagonal `p × p`
matrices and non-random diagonal `X_i` (the remark after Theorem 2, pp. 11–12, and §5.4,
pp. 24–25): the deterministic sharp sparsity oracle inequality for the Lasso.
Fixed design `x₁, …, xₙ ∈ ℝ^p`, `n ≥ 1`; a realization `Y = 𝕏β* + ξ`; `λ > 0` with
`λ ≥ 3‖M‖∞ = 3|(1/n) ∑_i ξ_i x_i|_∞`; `β̂` any minimizer of the Lasso criterion. Then for every
`β ∈ ℝ^p` and every `μ'` in the set defining `μ(β) = μ₅(β)`,
`(1/n)|𝕏(β̂ − β*)|_2² ≤ (1/n)|𝕏(β − β*)|_2² + λ² μ'² M(β)`.
Formalization Note: the infimum over `β` is "for every `β`"; `μ(β)` enters through its witnesses
(`IsMuWitness`), which is equivalent to using the infimum since the bound is continuous and
increasing in `μ'`; `rank(diag β) = M(β)`. -/
theorem theorem_2_lasso {n p : ℕ} (hn : 0 < n) (x : Fin n → Fin p → ℝ) (βstar : Fin p → ℝ)
    (ξ Y : Fin n → ℝ) (hY : ∀ i, Y i = ∑ j, x i j * βstar j + ξ i)
    {lam : ℝ} (hlam : 0 < lam) (hM : ∀ j, 3 * |noiseVec x ξ j| ≤ lam)
    {βhat : Fin p → ℝ} (hβhat : IsLasso x Y lam βhat) :
    ∀ (β : Fin p → ℝ) (μ' : ℝ), IsMuWitness x 5 β μ' →
      predLoss x βhat βstar ≤ predLoss x β βstar + lam ^ 2 * μ' ^ 2 * (sparsity β : ℝ) := by sorry

end KLTNuclear.Lasso
