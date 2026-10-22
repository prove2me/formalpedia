-- Prove2me | Theorems.Thm_ModernConvex_ConicDuality_weak_duality
-- name    : ModernConvex.ConicDuality.weak_duality
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-20T15:32:33.757608+00:00
-- url     : https://prove2.me/theorems/498c8b40-ee71-4e47-bba6-625a2d1d3361
-- title:
--   Proposition 2.3.1 — weak duality theorem
-- statement:
--   Let $\mathbf K \subset \mathbb R^m$ be a pointed closed convex cone with nonempty interior, let $A$ be an $m\times n$ matrix with linearly independent columns (Assumption A), and let $b \in \mathbb R^m$, $c \in \mathbb R^n$. Consider the conic problem and its dual
--   $$\text{(CP)}\ \min_x\{c^Tx \mid Ax - b \ge_{\mathbf K} 0\},\qquad \text{(D)}\ \max_\lambda\{b^T\lambda \mid A^T\lambda = c,\ \lambda \ge_{\mathbf K_*} 0\}.$$
--   The optimal value of (D) is a lower bound on the optimal value of (CP): for every feasible solution $x$ of (CP) and every feasible solution $\lambda$ of (D),
--   $$b^T\lambda \le c^Tx.$$
--
--   This is the first and easiest relation between a conic problem and its dual; strong duality (Theorem 2.4.1) builds on it.
--
--   **Formalization Note** The book compares optimal values in $[-\infty, +\infty]$; the Lean statement gives the equivalent pointwise form ($\sup$ of the dual objective $\le$ $\inf$ of the primal objective is the same as $b^T\lambda \le c^Tx$ for every feasible pair, with the conventions $\sup\emptyset = -\infty$, $\inf\emptyset = +\infty$). The cone conditions (p. 46) and Assumption A (p. 53) are the book's standing assumptions and appear as hypotheses.
-- source:
--   Ben-Tal & Nemirovski, Lectures on Modern Convex Optimization, SIAM 2001, p. 52, Proposition 2.3.1

import Mathlib
import Definitions.Def_ModernConvex_ConicDuality_ConicProblem

open Matrix

namespace ModernConvex.ConicDuality

/-- Ben-Tal–Nemirovski, Proposition 2.3.1 (weak duality theorem), p. 52: the optimal value of
`(D) : max { bᵀλ | Aᵀλ = c, λ ≥_{K∗} 0 }` is a lower bound on the optimal value of
`(CP) : min { cᵀx | Ax − b ≥_K 0 }`, stated pointwise: `bᵀλ ≤ cᵀx` for every dual feasible `λ`
and every primal feasible `x`. `K` is a good cone (p. 46) and Assumption A (p. 53) is in force. -/
theorem weak_duality {m n : ℕ} (K : Set (Fin m → ℝ)) (hK : IsGoodCone K)
    (A : Matrix (Fin m) (Fin n) ℝ) (hA : AssumptionA A) (b : Fin m → ℝ) (c : Fin n → ℝ) :
    ∀ (x : Fin n → ℝ) (l : Fin m → ℝ), PrimalFeasible K A b x → DualFeasible K A c l →
      b ⬝ᵥ l ≤ c ⬝ᵥ x := by sorry

end ModernConvex.ConicDuality
