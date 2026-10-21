-- Prove2me | Theorems.Thm_NatureSLT_Margin_kuhn_tucker_optimal_hyperplane
-- name    : NatureSLT.Margin.kuhn_tucker_optimal_hyperplane
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-20T15:51:43.513811+00:00
-- url     : https://prove2.me/theorems/f4a9dcfa-d8d9-46e0-9919-4e65ea3b87d0
-- title:
--   Eqs. (5.13)–(5.16) — Kühn–Tucker conditions characterize the optimal hyperplane
-- statement:
--   Let $(x_1, y_1), \dots, (x_\ell, y_\ell)$ be training data with $x_i \in \mathbb R^n$ and $y_i \in \{+1, -1\}$, belonging to both classes. Let $(w_0, b_0)$ satisfy the constraints
--
--   $$y_i[(x_i \cdot w_0) - b_0] \ge 1, \qquad i = 1, \dots, \ell. \tag{5.11}$$
--
--   Then $(w_0, b_0)$ is the optimal hyperplane, i.e. minimizes $\|w\|^2$ (equivalently $\tfrac12(w \cdot w)$ of (5.10)) over all $(w, b)$ satisfying (5.11), **if and only if** there are coefficients $\alpha^0_1, \dots, \alpha^0_\ell$ with
--
--   $$\sum_{i=1}^\ell \alpha^0_i y_i = 0, \quad \alpha^0_i \ge 0, \tag{5.13}$$
--
--   $$w_0 = \sum_{i=1}^\ell y_i \alpha^0_i x_i, \tag{5.14}$$
--
--   $$w_0 = \sum_{\text{support vectors}} y_i \alpha^0_i x_i, \tag{5.15}$$
--
--   $$\alpha^0_i\{[(x_i \cdot w_0) - b_0]\, y_i - 1\} = 0, \qquad i = 1, \dots, \ell. \tag{5.16}$$
--
--   The support vectors are the $x_i$ with $y_i[(x_i \cdot w_0) - b_0] = 1$.
--
--   These are the saddle-point conditions of the Lagrangian (5.12). They show that the optimal hyperplane is a nonnegative combination of the training vectors with only the support vectors carrying weight, which is what the dual problem (5.17)–(5.19) and the support vector machine exploit.
--
--   **Formalization Note** The book says the Kühn–Tucker conditions are "necessary and sufficient" for optimality; the statement is this equivalence, for a pair $(w_0, b_0)$ already satisfying (5.11). Both classes being present is the setting of Section 5.5 ("belonging to two different classes"). The sum in (5.15) is over the finite set of indices of support vectors of $(w_0, b_0)$.
-- source:
--   Vapnik, The Nature of Statistical Learning Theory, 2nd ed., Springer 2000, p. 134, Eqs. (5.13)–(5.16)

import Mathlib
import Definitions.Def_NatureSLT_Margin_optimalHyperplane
open scoped InnerProductSpace

namespace NatureSLT.Margin

/-- Vapnik, *The Nature of Statistical Learning Theory*, 2nd ed., §5.5, p. 134, (5.13)–(5.16):
by the Kühn–Tucker theorem, necessary and sufficient conditions for the separating hyperplane
`(w₀, b₀)` (satisfying (5.11)) to be the optimal hyperplane are that there exist coefficients
`α⁰₁, …, α⁰_ℓ` with
* (5.13) `∑ᵢ α⁰ᵢ yᵢ = 0`, `α⁰ᵢ ≥ 0`;
* (5.14) `w₀ = ∑ᵢ yᵢ α⁰ᵢ xᵢ`;
* (5.15) `w₀ = ∑_{support vectors} yᵢ α⁰ᵢ xᵢ`;
* (5.16) `α⁰ᵢ {[(xᵢ · w₀) − b₀] yᵢ − 1} = 0`, `i = 1, …, ℓ`.

Training data `(x₁, y₁), …, (x_ℓ, y_ℓ)`, `xᵢ ∈ ℝⁿ`, `yᵢ ∈ {+1, −1}`, both classes present
(§5.5: "belonging to two different classes"). Optimality is `IsOptimalHyperplane`
(minimizing `‖w‖²`, equivalently `½(w · w)` of (5.10), over `w` and `b` under (5.11)). -/
theorem kuhn_tucker_optimal_hyperplane {n ℓ : ℕ} (x : Fin ℓ → EuclideanSpace ℝ (Fin n))
    (y : Fin ℓ → ℝ) (hy : ∀ i, y i = 1 ∨ y i = -1) (hboth : (∃ i, y i = 1) ∧ ∃ j, y j = -1)
    (w₀ : EuclideanSpace ℝ (Fin n)) (b₀ : ℝ) (hsep : IsCanonicalSeparating x y w₀ b₀) :
    IsOptimalHyperplane x y w₀ b₀ ↔
      ∃ α₀ : Fin ℓ → ℝ, (∀ i, 0 ≤ α₀ i) ∧ ∑ i, α₀ i * y i = 0 ∧
        w₀ = ∑ i, (y i * α₀ i) • x i ∧
        w₀ = ∑ i ∈ supportVectors x y w₀ b₀, (y i * α₀ i) • x i ∧
        ∀ i, α₀ i * ((⟪x i, w₀⟫_ℝ - b₀) * y i - 1) = 0 := by sorry

end NatureSLT.Margin
