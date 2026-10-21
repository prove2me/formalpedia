-- Prove2me | Theorems.Thm_ModernConvex_ConicDuality_conic_duality_theorem
-- name    : ModernConvex.ConicDuality.conic_duality_theorem
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-20T15:32:27.138389+00:00
-- url     : https://prove2.me/theorems/c3317619-5252-4b0f-997e-7368ffc53488
-- title:
--   Theorem 2.4.1 — conic duality theorem (items 2, 3.a, 3.b, 4)
-- statement:
--   Let $\mathbf K \subset \mathbb R^m$ be a pointed closed convex cone with nonempty interior and $\mathbf K_* = \{\lambda : \lambda^Ta \ge 0\ \forall a \in \mathbf K\}$ its dual cone. Let $A$ be an $m \times n$ matrix with linearly independent columns (Assumption A), $b \in \mathbb R^m$, $c \in \mathbb R^n$. Consider the conic problem and its conic dual
--   $$c^* = \min_x\left\{c^Tx \mid Ax \ge_{\mathbf K} b\right\} \quad\text{(CP)}, \qquad b^* = \max_\lambda\left\{b^T\lambda \mid A^T\lambda = c,\ \lambda \ge_{\mathbf K_*} 0\right\} \quad\text{(D)}.$$
--   (CP) is strictly feasible if $Ax >_{\mathbf K} b$ (that is, $Ax - b \in \operatorname{int}\mathbf K$) for some $x$; (D) is strictly feasible if $A^T\lambda = c$ for some $\lambda >_{\mathbf K_*} 0$ (that is, $\lambda \in \operatorname{int}\mathbf K_*$). Then:
--
--   1. (Item 2.) The duality gap $c^Tx - b^T\lambda$ is nonnegative at every primal-dual feasible pair $(x, \lambda)$.
--   2. (Item 3.a.) If (CP) is bounded below and strictly feasible, then (D) is solvable and the optimal values are equal: there is a dual optimal $\lambda$ whose value $b^T\lambda$ is the infimum $c^*$ of $c^Tx$ over the feasible set of (CP).
--   3. (Item 3.b.) If (D) is bounded above and strictly feasible, then (CP) is solvable and $c^* = b^*$: there is a primal optimal $x$ whose value $c^Tx$ is the supremum $b^*$ of $b^T\lambda$ over the feasible set of (D).
--   4. (Item 4.) If at least one of (CP), (D) is bounded and strictly feasible, then a primal-dual feasible pair $(x, \lambda)$ is a pair of optimal solutions if and only if $b^T\lambda = c^Tx$ (zero duality gap), and if and only if $\lambda^T[Ax - b] = 0$ (complementary slackness).
--
--   This is the conic counterpart of the LP duality theorem; unlike LP, strict feasibility cannot be weakened to feasibility (the book's Examples 2.4.1 and 2.4.2 exhibit a strictly feasible, bounded problem without an optimal solution, and a solvable problem with an infeasible dual).
--
--   **Formalization Note** Item 1 of the book's theorem ("the duality is symmetric: the dual problem is conic, and the problem dual to dual is (equivalent to) the primal") is an informal equivalence of problems and is not part of this statement. "Bounded" in item 4 means bounded below for (CP) and bounded above for (D). Optimal values are never Lean reals with junk defaults: "$c^* = b^*$" is stated as "the optimal solution's value is the greatest lower bound (resp. least upper bound) of the other problem's feasible objective values". The book prints "$c_+ = b^*$" in 3.a; $c_+$ is a typo for $c^*$. The cone conditions (p. 46) and Assumption A (p. 53, in force "until the end of the book") are hypotheses.
-- source:
--   Ben-Tal & Nemirovski, Lectures on Modern Convex Optimization, SIAM 2001, pp. 57–58, Theorem 2.4.1

import Mathlib
import Definitions.Def_ModernConvex_ConicDuality_ConicProblem

open Matrix

namespace ModernConvex.ConicDuality

/-- Ben-Tal–Nemirovski, Theorem 2.4.1 (conic duality theorem), pp. 57–58, items 2, 3.a, 3.b and 4,
for `(CP) : c∗ = min { cᵀx | Ax ≥_K b }` and its conic dual
`(D) : b∗ = max { bᵀλ | Aᵀλ = c, λ ≥_{K∗} 0 }`, with `K` a pointed closed convex cone with
nonempty interior (p. 46) and `A` of full column rank (Assumption A, p. 53).
Item 1 (symmetry of the duality, informal) is not part of this statement. -/
theorem conic_duality_theorem {m n : ℕ} (K : Set (Fin m → ℝ)) (hK : IsGoodCone K)
    (A : Matrix (Fin m) (Fin n) ℝ) (hA : AssumptionA A) (b : Fin m → ℝ) (c : Fin n → ℝ) :
    -- 2. weak duality: the duality gap is nonnegative at every primal-dual feasible pair
    (∀ (x : Fin n → ℝ) (l : Fin m → ℝ), PrimalFeasible K A b x → DualFeasible K A c l →
      0 ≤ c ⬝ᵥ x - b ⬝ᵥ l) ∧
    -- 3.a. primal bounded below and strictly feasible ⇒ dual solvable and c∗ = b∗
    (PrimalBoundedBelow K A b c → PrimalStrictlyFeasible K A b →
      ∃ l : Fin m → ℝ, IsDualOptimal K A b c l ∧ IsPrimalOptimalValue K A b c (b ⬝ᵥ l)) ∧
    -- 3.b. dual bounded above and strictly feasible ⇒ primal solvable and c∗ = b∗
    (DualBoundedAbove K A b c → DualStrictlyFeasible K A c →
      ∃ x : Fin n → ℝ, IsPrimalOptimal K A b c x ∧ IsDualOptimalValue K A b c (c ⬝ᵥ x)) ∧
    -- 4. optimality ⇔ zero duality gap ⇔ complementary slackness
    ((PrimalBoundedBelow K A b c ∧ PrimalStrictlyFeasible K A b) ∨
        (DualBoundedAbove K A b c ∧ DualStrictlyFeasible K A c) →
      ∀ (x : Fin n → ℝ) (l : Fin m → ℝ), PrimalFeasible K A b x → DualFeasible K A c l →
        ((IsPrimalOptimal K A b c x ∧ IsDualOptimal K A b c l) ↔ b ⬝ᵥ l = c ⬝ᵥ x) ∧
        ((IsPrimalOptimal K A b c x ∧ IsDualOptimal K A b c l) ↔ l ⬝ᵥ (A *ᵥ x - b) = 0)) := by sorry

end ModernConvex.ConicDuality
