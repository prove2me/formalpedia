-- Prove2me | Theorems.Thm_ModernConvex_ConicDuality_both_strictly_feasible
-- name    : ModernConvex.ConicDuality.both_strictly_feasible
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-20T15:32:34.918688+00:00
-- url     : https://prove2.me/theorems/25e100e9-7d98-4c2f-b901-b31ba4831710
-- title:
--   Corollary 2.4.1 — both problems strictly feasible
-- statement:
--   Let $\mathbf K \subset \mathbb R^m$ be a pointed closed convex cone with nonempty interior, $A$ an $m \times n$ matrix with linearly independent columns (Assumption A), $b \in \mathbb R^m$, $c \in \mathbb R^n$, and let (CP) $\min\{c^Tx \mid Ax - b \ge_{\mathbf K} 0\}$ and (D) $\max\{b^T\lambda \mid A^T\lambda = c,\ \lambda \ge_{\mathbf K_*} 0\}$. Assume that both (CP) and (D) are strictly feasible. Then
--
--   1. both problems are solvable;
--   2. their optimal values are equal: some real $v$ is both the infimum of $c^Tx$ over the feasible set of (CP) and the supremum of $b^T\lambda$ over the feasible set of (D);
--   3. for every primal-dual feasible pair $(x, \lambda)$, the pair is optimal if and only if $b^T\lambda = c^Tx$, and if and only if $\lambda^T(Ax - b) = 0$.
--
--   This symmetric form is the version of conic duality most often used in applications.
--
--   **Formalization Note** "Strictly feasible" means $Ax - b \in \operatorname{int}\mathbf K$ for some $x$, and $A^T\lambda = c$ for some $\lambda \in \operatorname{int}\mathbf K_*$. Optimal values are expressed through `IsGLB`/`IsLUB` of the sets of feasible objective values. The cone conditions and Assumption A are hypotheses.
-- source:
--   Ben-Tal & Nemirovski, Lectures on Modern Convex Optimization, SIAM 2001, p. 60, Corollary 2.4.1

import Mathlib
import Definitions.Def_ModernConvex_ConicDuality_ConicProblem

open Matrix

namespace ModernConvex.ConicDuality

/-- Ben-Tal–Nemirovski, Corollary 2.4.1, p. 60: if both `(CP)` and `(D)` are strictly feasible,
both are solvable, their optimal values are equal, and each of the conditions 4.a (zero duality
gap) and 4.b (complementary slackness) of Theorem 2.4.1 is necessary and sufficient for optimality
of a primal-dual feasible pair. `K` is a good cone (p. 46) and Assumption A (p. 53) is in force. -/
theorem both_strictly_feasible {m n : ℕ} (K : Set (Fin m → ℝ)) (hK : IsGoodCone K)
    (A : Matrix (Fin m) (Fin n) ℝ) (hA : AssumptionA A) (b : Fin m → ℝ) (c : Fin n → ℝ)
    (hP : PrimalStrictlyFeasible K A b) (hD : DualStrictlyFeasible K A c) :
    PrimalSolvable K A b c ∧ DualSolvable K A b c ∧
    (∃ v : ℝ, IsPrimalOptimalValue K A b c v ∧ IsDualOptimalValue K A b c v) ∧
    (∀ (x : Fin n → ℝ) (l : Fin m → ℝ), PrimalFeasible K A b x → DualFeasible K A c l →
      ((IsPrimalOptimal K A b c x ∧ IsDualOptimal K A b c l) ↔ b ⬝ᵥ l = c ⬝ᵥ x) ∧
      ((IsPrimalOptimal K A b c x ∧ IsDualOptimal K A b c l) ↔ l ⬝ᵥ (A *ᵥ x - b) = 0)) := by sorry

end ModernConvex.ConicDuality
