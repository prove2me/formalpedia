-- Prove2me | Theorems.Thm_ModernConvex_ConicDuality_duality_gap_identity
-- name    : ModernConvex.ConicDuality.duality_gap_identity
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-20T15:32:27.055726+00:00
-- url     : https://prove2.me/theorems/8cb0697f-0c86-4e4c-9cb7-cd51449886d0
-- title:
--   Proposition 2.4.1 — the duality gap equals the inner product of the primal slack and the dual vector
-- statement:
--   Let $\mathbf K \subset \mathbb R^m$ be a pointed closed convex cone with nonempty interior, $A$ an $m\times n$ matrix with linearly independent columns (Assumption A), $b \in \mathbb R^m$, $c \in \mathbb R^n$, and let (CP) $\min\{c^Tx \mid Ax - b \ge_{\mathbf K} 0\}$ and (D) $\max\{b^T\lambda \mid A^T\lambda = c,\ \lambda \ge_{\mathbf K_*} 0\}$ be the conic problem and its dual. For every primal-dual feasible pair $(x, \lambda)$ the duality gap equals the inner product of the primal slack vector $y = Ax - b$ and the dual vector $\lambda$:
--   $$c^Tx - b^T\lambda = (Ax - b)^T\lambda.$$
--
--   It is the identity through which complementary slackness (item 4.b of Theorem 2.4.1) is equivalent to a zero duality gap.
--
--   **Formalization Note** The cone conditions (p. 46) and Assumption A (p. 53) are the book's standing assumptions and appear as hypotheses, although the identity only uses $A^T\lambda = c$.
-- source:
--   Ben-Tal & Nemirovski, Lectures on Modern Convex Optimization, SIAM 2001, p. 59, Proposition 2.4.1

import Mathlib
import Definitions.Def_ModernConvex_ConicDuality_ConicProblem

open Matrix

namespace ModernConvex.ConicDuality

/-- Ben-Tal–Nemirovski, Proposition 2.4.1, p. 59: for every primal-dual feasible pair `(x, λ)` of
`(CP)` and `(D)` the duality gap `cᵀx − bᵀλ` equals the inner product of the primal slack
`y = Ax − b` with `λ`. `K` is a good cone (p. 46) and Assumption A (p. 53) is in force. -/
theorem duality_gap_identity {m n : ℕ} (K : Set (Fin m → ℝ)) (hK : IsGoodCone K)
    (A : Matrix (Fin m) (Fin n) ℝ) (hA : AssumptionA A) (b : Fin m → ℝ) (c : Fin n → ℝ) :
    ∀ (x : Fin n → ℝ) (l : Fin m → ℝ), PrimalFeasible K A b x → DualFeasible K A c l →
      c ⬝ᵥ x - b ⬝ᵥ l = (A *ᵥ x - b) ⬝ᵥ l := by sorry

end ModernConvex.ConicDuality
