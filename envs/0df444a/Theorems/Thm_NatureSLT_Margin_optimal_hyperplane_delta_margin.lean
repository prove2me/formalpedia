-- Prove2me | Theorems.Thm_NatureSLT_Margin_optimal_hyperplane_delta_margin
-- name    : NatureSLT.Margin.optimal_hyperplane_delta_margin
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-20T15:51:57.542278+00:00
-- url     : https://prove2.me/theorems/9475ec2b-1b76-45de-92bd-f20bf83f448c
-- title:
--   Section 5.4.2 — the optimal hyperplane is the Δ-margin separating hyperplane with Δ = 1/|w₀|
-- statement:
--   Let $(x_1, y_1), \dots, (x_\ell, y_\ell)$ be training data with $x_i \in \mathbb R^n$ and $y_i \in \{+1, -1\}$, both classes present. Let $(w_0, b_0)$ be the optimal hyperplane in canonical form: it satisfies $y_i[(w_0 \cdot x_i) - b_0] \ge 1$ for all $i$ (5.8) and minimizes $\|w\|^2$ over all $(w, b)$ satisfying (5.8). Then $w_0 \ne 0$, and the same hyperplane written with a unit normal,
--
--   $$w^* = \frac{w_0}{|w_0|}, \qquad b = \frac{b_0}{|w_0|}, \qquad |w^*| = 1,$$
--
--   is a $\Delta$-margin separating hyperplane with
--
--   $$\Delta = \frac{1}{|w_0|}$$
--
--   that classifies every training vector correctly: $(w^* \cdot x_i) - b \ge \Delta$ when $y_i = 1$ and $(w^* \cdot x_i) - b \le -\Delta$ when $y_i = -1$.
--
--   This links the optimal hyperplane of Section 5.4.1 with the $\Delta$-margin hyperplanes whose VC dimension Theorem 5.1 bounds.
--
--   **Formalization Note** The book prints "$\Delta = 1/|w^*|$". Since $|w^*| = 1$ in the definition of a $\Delta$-margin hyperplane, that would read $\Delta = 1$, which is false in general (F2 in the mission's findings). The $w^*$ in that sentence is the canonical vector $w_0$ of (5.8), and the statement uses $\Delta = 1/|w_0|$. Labels are real numbers $\pm 1$; the label passed to the $\Delta$-margin classification is the boolean "$y_i = 1$".
-- source:
--   Vapnik, The Nature of Statistical Learning Theory, 2nd ed., Springer 2000, p. 132, Section 5.4.2

import Mathlib
import Definitions.Def_NatureSLT_Margin_optimalHyperplane
import Definitions.Def_NatureSLT_Margin_marginVCDim

namespace NatureSLT.Margin

/-- Vapnik, *The Nature of Statistical Learning Theory*, 2nd ed., §5.4.2, p. 132: the optimal
hyperplane defined in canonical form (5.8) is the Δ-margin separating hyperplane with
`Δ = 1/|w₀|`.

Training data `(x₁, y₁), …, (x_ℓ, y_ℓ)`, `xᵢ ∈ ℝⁿ`, `yᵢ ∈ {+1, −1}`, both classes present; `(w₀, b₀)`
is the optimal hyperplane (satisfies (5.8) and minimizes `‖w‖²`). Then `w₀ ≠ 0`, and the same
hyperplane written with a unit normal, `w* = w₀/|w₀|`, `b = b₀/|w₀|`, is a Δ-margin separating
hyperplane with `Δ = 1/|w₀|` that classifies every training vector `xᵢ` with its label `yᵢ`.
The book prints `Δ = 1/|w*|`, which with `|w*| = 1` would read `Δ = 1`; the `w*` there is the
canonical vector `w₀` of (5.8). Labels are real here and `Bool` in `MarginClassifies`
(`true` ↔ `yᵢ = 1`). -/
theorem optimal_hyperplane_delta_margin {n ℓ : ℕ} (x : Fin ℓ → EuclideanSpace ℝ (Fin n))
    (y : Fin ℓ → ℝ) (hy : ∀ i, y i = 1 ∨ y i = -1) (hboth : (∃ i, y i = 1) ∧ ∃ j, y j = -1)
    (w₀ : EuclideanSpace ℝ (Fin n)) (b₀ : ℝ) (hopt : IsOptimalHyperplane x y w₀ b₀) :
    w₀ ≠ 0 ∧ ‖‖w₀‖⁻¹ • w₀‖ = 1 ∧
      ∀ i, MarginClassifies (‖w₀‖⁻¹ • w₀) (b₀ / ‖w₀‖) (1 / ‖w₀‖) (x i) (decide (y i = 1)) := by sorry

end NatureSLT.Margin
