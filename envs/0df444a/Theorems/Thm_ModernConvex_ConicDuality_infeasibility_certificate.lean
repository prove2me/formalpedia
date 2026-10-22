-- Prove2me | Theorems.Thm_ModernConvex_ConicDuality_infeasibility_certificate
-- name    : ModernConvex.ConicDuality.infeasibility_certificate
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-20T15:32:34.060498+00:00
-- url     : https://prove2.me/theorems/dcaa3901-a1b9-49a4-90cf-55bdf210bd21
-- title:
--   Proposition 2.4.2 — certificates of infeasibility and almost solvability of a conic inequality
-- statement:
--   Let $\mathbf K \subset \mathbb R^m$ be a pointed closed convex cone with nonempty interior, $A$ an $m\times n$ matrix with linearly independent columns (Assumption A), and $b \in \mathbb R^m$. Consider the linear vector inequality and the associated system
--   $$\text{(I)}\quad Ax - b \ge_{\mathbf K} 0, \qquad\qquad \text{(II)}\quad \lambda \ge_{\mathbf K_*} 0,\ \ A^T\lambda = 0,\ \ \lambda^Tb > 0.$$
--   Call (I) **almost solvable** if for every $\epsilon > 0$ there is $b'$ with $\|b' - b\|_2 < \epsilon$ such that $Ax - b' \ge_{\mathbf K} 0$ is solvable. Then:
--
--   1. If (II) has a solution, then (I) has no solutions.
--   2. If (II) has no solutions, then (I) is almost solvable.
--   3. (II) is solvable if and only if (I) is not almost solvable.
--
--   This is the conic analogue of the theorem on alternatives for linear inequalities; unlike the LP case, "almost solvable" in item 2 cannot be replaced by "solvable" (Example 2.4.3, p. 62).
--
--   **Formalization Note** $\|b' - b\|_2$ is written $\sqrt{\sum_i (b'_i - b_i)^2}$. The book's Remark 2.4.1 (p. 64) states that the results of §2.4.2 are obtained under Assumption A, so full column rank of $A$ is a hypothesis, as are the cone conditions of p. 46.
-- source:
--   Ben-Tal & Nemirovski, Lectures on Modern Convex Optimization, SIAM 2001, pp. 61–62, Proposition 2.4.2

import Mathlib
import Definitions.Def_ModernConvex_ConicDuality_ConicProblem

open Matrix

namespace ModernConvex.ConicDuality

/-- Ben-Tal–Nemirovski, Proposition 2.4.2, pp. 61–62, for the linear vector inequality
`(I) : Ax − b ≥_K 0` and the system `(II) : λ ≥_{K∗} 0, Aᵀλ = 0, λᵀb > 0`.
(I) is *almost solvable* when for every `ε > 0` some `b′` with `‖b′ − b‖₂ < ε` makes
`Ax − b′ ≥_K 0` solvable.
(i) If (II) is solvable, (I) has no solutions. (ii) If (II) has no solutions, (I) is almost
solvable. (iii) (II) is solvable iff (I) is not almost solvable.
`K` is a good cone (p. 46); Assumption A (p. 53) is in force by Remark 2.4.1 (p. 64). -/
theorem infeasibility_certificate {m n : ℕ} (K : Set (Fin m → ℝ)) (hK : IsGoodCone K)
    (A : Matrix (Fin m) (Fin n) ℝ) (hA : AssumptionA A) (b : Fin m → ℝ) :
    -- (i)
    ((∃ l : Fin m → ℝ, l ∈ dualCone K ∧ Aᵀ *ᵥ l = 0 ∧ 0 < l ⬝ᵥ b) →
      ¬ ∃ x : Fin n → ℝ, A *ᵥ x - b ∈ K) ∧
    -- (ii)
    ((¬ ∃ l : Fin m → ℝ, l ∈ dualCone K ∧ Aᵀ *ᵥ l = 0 ∧ 0 < l ⬝ᵥ b) →
      ∀ ε : ℝ, 0 < ε → ∃ b' : Fin m → ℝ, Real.sqrt (∑ i, (b' i - b i) ^ 2) < ε ∧
        ∃ x : Fin n → ℝ, A *ᵥ x - b' ∈ K) ∧
    -- (iii)
    ((∃ l : Fin m → ℝ, l ∈ dualCone K ∧ Aᵀ *ᵥ l = 0 ∧ 0 < l ⬝ᵥ b) ↔
      ¬ ∀ ε : ℝ, 0 < ε → ∃ b' : Fin m → ℝ, Real.sqrt (∑ i, (b' i - b i) ^ 2) < ε ∧
        ∃ x : Fin n → ℝ, A *ᵥ x - b' ∈ K) := by sorry

end ModernConvex.ConicDuality
