-- Prove2me | Theorems.Thm_KLTNuclear_Lasso_cone_step
-- name    : KLTNuclear.Lasso.cone_step
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T07:52:24.022762+00:00
-- url     : https://prove2.me/theorems/0d9999da-59b1-40e0-8780-a2e58cf4de92
-- title:
--   (2.20)–(2.22), p. 11 — for diagonal matrices the Lasso error lies in the cone |u_{Jᶜ}|₁ ≤ 5|u_J|₁
-- statement:
--   Let $x_1,\dots,x_n\in\mathbb R^p$ be a fixed design, $n \ge 1$, $\beta^*\in\mathbb R^p$, $\xi\in\mathbb R^n$, and $Y_i = x_i^\top\beta^* + \xi_i$. Let $\lambda > 0$ satisfy
--   $$
--   \lambda \ge 3\,\|\mathbf M\|_\infty = 3\,\Big|\frac1n\sum_{i=1}^n\xi_ix_i\Big|_\infty ,
--   $$
--   and let $\hat\beta$ be a Lasso estimator with this $\lambda$. Fix $\beta\in\mathbb R^p$ with support $J = \{j : \beta(j)\neq0\}$. If
--   $$
--   \langle \hat\beta-\beta^*, \hat\beta-\beta\rangle_{L_2(\Pi)} = \frac1n\sum_{i=1}^n x_i^\top(\hat\beta-\beta^*)\,x_i^\top(\hat\beta-\beta) > 0,
--   $$
--   then
--   $$
--   |(\hat\beta-\beta)_{J^c}|_1 \le 5\,|(\hat\beta-\beta)_J|_1 ,
--   $$
--   that is, $\operatorname{diag}(\hat\beta-\beta)$ lies in the cone $\mathbb C_{\operatorname{diag}\beta,5}$.
--
--   This is the step of the proof of Theorem 2 where the cone constant $5$ comes from: it is what makes $\mu(\beta) = \mu_5(\beta)$ the right restricted constant.
--
--   **Formalization Note** The page states this for a matrix $A$ in a linear subspace $\mathbb A$; this is its diagonal case with fixed design, in the vector form computed on p. 26. The noise is a fixed vector, so $\mathbf M = \frac1n\sum_i\xi_ix_i$ (the expectation of $Y_iX_i$ is $\langle A_0,X_i\rangle X_i$ for fixed $X_i$ and centred noise). $\|\mathbf M\|_\infty \le \lambda/3$ is written coordinatewise. $\lambda > 0$ is the paper's standing assumption (p. 4).
-- source:
--   Koltchinskii, Lounici, Tsybakov, Nuclear-Norm Penalization and Optimal Rates for Noisy Low-Rank Matrix Completion, arXiv:1011.6256v4, p. 11, proof of Theorem 2, (2.20)–(2.22) and the display after 'For λ ≥ 3Δ, this yields'; diagonal case: remark after Theorem 2, pp. 11–12, and p. 26

import Mathlib
import Definitions.Def_KLTNuclear_Lasso_Model

namespace KLTNuclear.Lasso

/-- (2.20)–(2.22) in the proof of Theorem 2, arXiv:1011.6256v4, p. 11, for diagonal matrices
(the Lasso, pp. 11–12, 24–25). Fixed design `x₁, …, xₙ ∈ ℝ^p`, `n ≥ 1`; a realization
`Y = 𝕏β* + ξ` of the linear model; `λ > 0` with `λ ≥ 3|(1/n) ∑_i ξ_i x_i|_∞`; `β̂` a minimizer of
the Lasso criterion. Let `β ∈ ℝ^p` and `J = {j : β(j) ≠ 0}`. If
`⟨β̂ − β*, β̂ − β⟩_{L₂(Π)} = (1/n) ∑_i x_iᵀ(β̂ − β*) · x_iᵀ(β̂ − β) > 0`, then
`|(β̂ − β)_{Jᶜ}|_1 ≤ 5 |(β̂ − β)_J|_1`, i.e. `diag(β̂ − β) ∈ ℂ_{diag β, 5}`.
Formalization Note: `‖M‖∞ ≤ λ/3` is written coordinatewise. -/
theorem cone_step {n p : ℕ} (hn : 0 < n) (x : Fin n → Fin p → ℝ) (βstar : Fin p → ℝ)
    (ξ Y : Fin n → ℝ) (hY : ∀ i, Y i = ∑ j, x i j * βstar j + ξ i)
    {lam : ℝ} (hlam : 0 < lam) (hM : ∀ j, 3 * |noiseVec x ξ j| ≤ lam)
    {βhat : Fin p → ℝ} (hβhat : IsLasso x Y lam βhat) (β : Fin p → ℝ)
    (hcase : 0 < (1 / (n : ℝ)) * ∑ i, design x (βhat - βstar) i * design x (βhat - β) i) :
    l1On (βhat - β) (supp β)ᶜ ≤ 5 * l1On (βhat - β) (supp β) := by sorry

end KLTNuclear.Lasso
