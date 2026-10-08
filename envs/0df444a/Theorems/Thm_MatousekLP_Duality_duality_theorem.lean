-- Prove2me | Theorems.Thm_MatousekLP_Duality_duality_theorem
-- name    : MatousekLP.Duality.duality_theorem
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-03T11:16:56.801971+00:00
-- url     : https://prove2.me/theorems/21b72a2b-a2ac-44a9-9f14-cd3705cd9ca9
-- title:
--   Duality theorem (§6.1) — the duality theorem of linear programming
-- statement:
--   Let $A$ be a real matrix with $m$ rows and $n$ columns, $b\in\mathbb{R}^m$ and $c\in\mathbb{R}^n$, and consider the linear programs
--
--   $$\text{(P)}\quad \text{maximize } c^{T}x \ \text{ subject to } Ax\le b,\ x\ge 0, \qquad\qquad \text{(D)}\quad \text{minimize } b^{T}y \ \text{ subject to } A^{T}y\ge c,\ y\ge 0.$$
--
--   Then exactly one of the following four possibilities occurs:
--
--   1. neither (P) nor (D) has a feasible solution;
--   2. (P) is unbounded and (D) has no feasible solution;
--   3. (P) has no feasible solution and (D) is unbounded (from below);
--   4. both (P) and (D) have a feasible solution; then both have an optimal solution, and for every optimal solution $x^*$ of (P) and every optimal solution $y^*$ of (D)
--   $$c^{T}x^*=b^{T}y^*.$$
--
--   That is, whenever both programs are feasible, the maximum of (P) is attained and equals the minimum of (D), which is attained as well. This is the central theorem of linear programming duality; weak duality (Proposition 6.1.1) supplies the inequality $c^{T}x\le b^{T}y$, and the content of the theorem is that the dual guards the primal perfectly.
--
--   **Formalization Note** The four cases are the predicate `DualityCase A b c k` of the definition module `MatousekLP.Duality.PrimalDual`, with the book's case $k$ at index $k-1\in\{0,1,2,3\}$; "exactly one occurs" is `∃! k : Fin 4, DualityCase A b c k`. Optimal solutions are feasible points whose objective value is at least (for (P)) or at most (for (D)) that of every feasible point; no supremum or infimum is used.
-- source:
--   Matoušek & Gärtner, Understanding and Using Linear Programming, Springer 2007, §6.1, p. 83, Duality theorem of linear programming

import Mathlib
import Definitions.Def_MatousekLP_Duality_PrimalDual

namespace MatousekLP.Duality

/-- Matoušek & Gärtner, §6.1, p. 83, Duality theorem of linear programming: for
(P) maximize `cᵀx` s.t. `Ax ≤ b`, `x ≥ 0` and (D) minimize `bᵀy` s.t. `Aᵀy ≥ c`, `y ≥ 0`,
exactly one of the four possibilities `DualityCase A b c k` (`k = 0, 1, 2, 3` for the book's
cases 1–4) occurs. -/
theorem duality_theorem {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ)
    (c : Fin n → ℝ) :
    ∃! k : Fin 4, DualityCase A b c k := by sorry

end MatousekLP.Duality
