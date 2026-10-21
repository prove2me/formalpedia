-- Prove2me | Theorems.Thm_NatureSLT_Margin_optimal_hyperplane_max_margin
-- name    : NatureSLT.Margin.optimal_hyperplane_max_margin
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-20T15:51:44.865435+00:00
-- url     : https://prove2.me/theorems/cdeb643e-549a-412d-9aec-e14816bf71f6
-- title:
--   Section 5.4.1 — the maximal margin hyperplane is the canonical hyperplane (5.8) minimizing ‖w‖² (5.9)
-- statement:
--   Let $(x_1, y_1), \dots, (x_\ell, y_\ell)$ be training data with $x_i \in \mathbb R^n$ and $y_i \in \{+1, -1\}$, both classes present. A hyperplane $(w \cdot x) - b = 0$ with $w \neq 0$ **separates the data without error** if $y_i[(w \cdot x_i) - b] > 0$ for all $i$. Its **margin** is the distance from the closest training vector to the hyperplane:
--
--   $$\rho(w, b) = \min_{i} \operatorname{dist}\bigl(x_i, \{v : (w \cdot v) - b = 0\}\bigr).$$
--
--   The optimal (maximal margin) hyperplane separates the data without error and has maximal margin. Its characterization through the canonical problem (5.8)–(5.9) consists of two claims.
--
--   1. If $(w_0, b_0)$ satisfies $y_i[(w_0 \cdot x_i) - b_0] \ge 1$ for all $i$ and minimizes $\|w\|^2$ over all $(w, b)$ satisfying these constraints, then $w_0 \neq 0$, $(w_0, b_0)$ separates the data without error, and $\rho(w, b) \le \rho(w_0, b_0)$ for every hyperplane $(w, b)$, $w \ne 0$, that separates the data without error.
--   2. Conversely, let $(w, b)$, $w \neq 0$, separate the data without error with maximal margin among all such hyperplanes, and put $\mu = \min_i y_i[(w \cdot x_i) - b] > 0$. Then the rescaled pair $(w/\mu, b/\mu)$ satisfies (5.8) and minimizes $\|w\|^2$ under (5.8).
--
--   This is the reduction of margin maximization to the quadratic program (5.10)–(5.11) on which the construction of support vector machines rests.
--
--   **Formalization Note** The distance to the hyperplane is the infimum distance from the point to the set $\{v : (w \cdot v) - b = 0\}$, and the minimum over the finitely many training vectors is a real infimum over a nonempty finite index set. The book states the equivalence in one sentence ("the optimal hyperplane is the one that satisfies the conditions (5.8) and minimizes $\Phi(w)$"); both directions are stated, the second with the rescaling that brings a hyperplane to canonical form. Both classes being present is the setting of Section 5.4.1 (labels $\pm1$).
-- source:
--   Vapnik, The Nature of Statistical Learning Theory, 2nd ed., Springer 2000, pp. 131–132, Section 5.4.1, Eqs. (5.8)–(5.9)

import Mathlib
import Definitions.Def_NatureSLT_Margin_optimalHyperplane
open scoped InnerProductSpace

namespace NatureSLT.Margin

/-- Vapnik, *The Nature of Statistical Learning Theory*, 2nd ed., §5.4.1, p. 132, the claim after
(5.8)–(5.9): the optimal hyperplane, i.e. the hyperplane that separates the training data without
error and for which the distance between the closest vector and the hyperplane is maximal, is the
one that satisfies the conditions (5.8) and minimizes `Φ(w) = ‖w‖²` over `w` and `b`.

Training data `(x₁, y₁), …, (x_ℓ, y_ℓ)`, `xᵢ ∈ ℝⁿ`, `yᵢ ∈ {+1, −1}`, with both classes present.
The distance of `xᵢ` to the hyperplane `(w · x) − b = 0` is `Metric.infDist`. Both directions are
stated:
1. a minimizer `(w₀, b₀)` of `‖w‖²` under (5.8) separates the data without error, and no
   hyperplane `(w, b)` (`w ≠ 0`) that separates the data without error has a larger distance from
   its closest training vector;
2. conversely, a hyperplane `(w, b)` (`w ≠ 0`) that separates the data without error with maximal
   distance of the closest vector, rescaled to canonical form by
   `μ = minᵢ yᵢ[(w · xᵢ) − b] > 0`, is a minimizer of `‖w‖²` under (5.8). -/
theorem optimal_hyperplane_max_margin {n ℓ : ℕ} (x : Fin ℓ → EuclideanSpace ℝ (Fin n))
    (y : Fin ℓ → ℝ) (hy : ∀ i, y i = 1 ∨ y i = -1) (hboth : (∃ i, y i = 1) ∧ ∃ j, y j = -1) :
    (∀ (w₀ : EuclideanSpace ℝ (Fin n)) (b₀ : ℝ), IsOptimalHyperplane x y w₀ b₀ →
      w₀ ≠ 0 ∧ (∀ i, 0 < y i * (⟪w₀, x i⟫_ℝ - b₀)) ∧
      ∀ (w : EuclideanSpace ℝ (Fin n)) (b : ℝ), w ≠ 0 → (∀ i, 0 < y i * (⟪w, x i⟫_ℝ - b)) →
        (⨅ i, Metric.infDist (x i) {v | ⟪w, v⟫_ℝ - b = 0}) ≤
          ⨅ i, Metric.infDist (x i) {v | ⟪w₀, v⟫_ℝ - b₀ = 0}) ∧
    (∀ (w : EuclideanSpace ℝ (Fin n)) (b : ℝ), w ≠ 0 → (∀ i, 0 < y i * (⟪w, x i⟫_ℝ - b)) →
      (∀ (w' : EuclideanSpace ℝ (Fin n)) (b' : ℝ), w' ≠ 0 →
        (∀ i, 0 < y i * (⟪w', x i⟫_ℝ - b')) →
        (⨅ i, Metric.infDist (x i) {v | ⟪w', v⟫_ℝ - b' = 0}) ≤
          ⨅ i, Metric.infDist (x i) {v | ⟪w, v⟫_ℝ - b = 0}) →
      IsOptimalHyperplane x y ((⨅ i, y i * (⟪w, x i⟫_ℝ - b))⁻¹ • w)
        ((⨅ i, y i * (⟪w, x i⟫_ℝ - b))⁻¹ * b)) := by sorry

end NatureSLT.Margin
