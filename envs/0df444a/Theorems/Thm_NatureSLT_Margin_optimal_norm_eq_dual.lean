-- Prove2me | Theorems.Thm_NatureSLT_Margin_optimal_norm_eq_dual
-- name    : NatureSLT.Margin.optimal_norm_eq_dual
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-20T15:51:42.871717+00:00
-- url     : https://prove2.me/theorems/cb3e1381-ddbf-4cf6-9f5c-dfbe9037f04f
-- title:
--   Section 5.5, display after (5.19) — |w₀|² = 2W(α₀) = Σ_{support vectors} α⁰ᵢα⁰ⱼ(xᵢ·xⱼ)yᵢyⱼ
-- statement:
--   Let $(x_1, y_1), \dots, (x_\ell, y_\ell)$ be training data with $x_i \in \mathbb R^n$ and $y_i \in \{+1, -1\}$, both classes present. Let $(w_0, b_0)$ be the optimal hyperplane: it satisfies $y_i[(w_0 \cdot x_i) - b_0] \ge 1$ for all $i$ and minimizes $\|w\|^2$ under these constraints. Let
--
--   $$W(\alpha) = \sum_{i=1}^\ell \alpha_i - \frac12 \sum_{i,j=1}^\ell \alpha_i \alpha_j y_i y_j (x_i \cdot x_j) \tag{5.17}$$
--
--   and let $\alpha_0 = (\alpha^0_1, \dots, \alpha^0_\ell)$ be a solution of the quadratic programming problem: maximize $W(\alpha)$ in the nonnegative quadrant $\alpha_i \ge 0$ (5.18) under the constraint $\sum_i \alpha_i y_i = 0$ (5.19). Then
--
--   $$|w_0|^2 = 2W(\alpha_0) = \sum_{\text{support vectors}} \alpha^0_i \alpha^0_j (x_i \cdot x_j) y_i y_j,$$
--
--   where the double sum runs over all pairs $i, j$ of indices of support vectors of $(w_0, b_0)$, the $x_i$ with $y_i[(x_i \cdot w_0) - b_0] = 1$.
--
--   The identity computes the margin $1/|w_0|$ of the optimal hyperplane from the solution of the dual problem alone. This is the quantity that enters the bound $[R^2|w|^2]$ of Theorem 5.2.
--
--   **Formalization Note** The optimal hyperplane $(w_0, b_0)$ and the dual solution $\alpha_0$ are both hypotheses (the book introduces them as "the" solutions); nothing here asserts that they exist. The sum over support vectors is the double sum over the finite set of support-vector indices of $(w_0, b_0)$.
-- source:
--   Vapnik, The Nature of Statistical Learning Theory, 2nd ed., Springer 2000, p. 135, Section 5.5, display after (5.19)

import Mathlib
import Definitions.Def_NatureSLT_Margin_optimalHyperplane
open scoped InnerProductSpace

namespace NatureSLT.Margin

/-- Vapnik, *The Nature of Statistical Learning Theory*, 2nd ed., §5.5, p. 135, display after
(5.19): let `α₀ = (α⁰₁, …, α⁰_ℓ)` be a solution of the quadratic optimization problem
"maximize `W(α)` of (5.17) in the nonnegative quadrant (5.18) `αᵢ ≥ 0` under the constraint (5.19)
`∑ᵢ αᵢ yᵢ = 0`". Then the norm of the vector `w₀` corresponding to the optimal hyperplane equals
`|w₀|² = 2W(α₀) = ∑_{support vectors} α⁰ᵢ α⁰ⱼ (xᵢ · xⱼ) yᵢ yⱼ`.

Training data `(x₁, y₁), …, (x_ℓ, y_ℓ)`, `xᵢ ∈ ℝⁿ`, `yᵢ ∈ {+1, −1}`, both classes present;
`(w₀, b₀)` is the optimal hyperplane; the double sum runs over pairs `i, j` of support vectors of
`(w₀, b₀)`. -/
theorem optimal_norm_eq_dual {n ℓ : ℕ} (x : Fin ℓ → EuclideanSpace ℝ (Fin n))
    (y : Fin ℓ → ℝ) (hy : ∀ i, y i = 1 ∨ y i = -1) (hboth : (∃ i, y i = 1) ∧ ∃ j, y j = -1)
    (w₀ : EuclideanSpace ℝ (Fin n)) (b₀ : ℝ) (hopt : IsOptimalHyperplane x y w₀ b₀)
    (α₀ : Fin ℓ → ℝ) (hα₀ : (∀ i, 0 ≤ α₀ i) ∧ ∑ i, α₀ i * y i = 0)
    (hmax : ∀ α : Fin ℓ → ℝ, (∀ i, 0 ≤ α i) → ∑ i, α i * y i = 0 → dualW x y α ≤ dualW x y α₀) :
    ‖w₀‖ ^ 2 = 2 * dualW x y α₀ ∧
      2 * dualW x y α₀ = ∑ i ∈ supportVectors x y w₀ b₀, ∑ j ∈ supportVectors x y w₀ b₀,
        α₀ i * α₀ j * ⟪x i, x j⟫_ℝ * y i * y j := by sorry

end NatureSLT.Margin
