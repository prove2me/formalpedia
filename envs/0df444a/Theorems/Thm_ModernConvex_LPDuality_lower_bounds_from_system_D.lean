-- Prove2me | Theorems.Thm_ModernConvex_LPDuality_lower_bounds_from_system_D
-- name    : ModernConvex.LPDuality.lower_bounds_from_system_D
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-20T15:32:22.030462+00:00
-- url     : https://prove2.me/theorems/33333d49-e402-46f2-aab0-702559d0bed1
-- title:
--   Proposition 1.3.2 — solutions $(y,a)$ of (D) are exactly the lower bounds $a$ on the optimal value of a feasible (LP)
-- statement:
--   Consider the LP program $\text{(LP)}\ \min_x\{c^Tx \mid Ax \ge b\}$ with $A \in \mathbb R^{m\times n}$ (rows $a_i^T$), $b \in \mathbb R^m$, $c \in \mathbb R^n$, and the associated system (D) in the unknowns $y \in \mathbb R^m$, $a \in \mathbb R$:
--   $$y \ge 0, \qquad A^Ty \equiv \sum_{i=1}^m y_ia_i = c, \qquad b^Ty \ge a.$$
--   Then:
--
--   1. if (D) has a solution $(y, a)$, then $a$ is a lower bound on the optimal value of (LP), that is, $c^Tx \ge a$ for every $x$ with $Ax \ge b$;
--   2. if (LP) is feasible and $a$ is a lower bound on the optimal value of (LP), then there is $y \in \mathbb R^m$ such that $(y, a)$ solves (D).
--
--   This is the statement from which the book defines the dual problem (LP$^*$): the best lower bound obtainable from (D) is $\max\{b^Ty \mid A^Ty = c,\ y \ge 0\}$.
--
--   **Formalization Note** "$a$ is a lower bound on the optimal value" is the predicate $\forall x,\ Ax \ge b \Rightarrow a \le c^Tx$ (p. 16), which avoids giving the possibly infinite optimal value a real junk value.
-- source:
--   Ben-Tal & Nemirovski, Lectures on Modern Convex Optimization, SIAM 2001, p. 17, Proposition 1.3.2, system (D)

import Mathlib
import Definitions.Def_ModernConvex_LPDuality_LinearProgram

open Matrix

namespace ModernConvex.LPDuality

/-- Ben-Tal–Nemirovski, Proposition 1.3.2, p. 17: every solution `(y, a)` of `(D)` gives a lower
bound `a` on the optimal value of `(LP)`; if `(LP)` is feasible, every lower bound `a` extends
to a solution `(y, a)` of `(D)`. -/
theorem lower_bounds_from_system_D {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ)
    (c : Fin n → ℝ) :
    (∀ (y : Fin m → ℝ) (a : ℝ), SystemD A b c y a → IsPrimalLowerBound A b c a) ∧
    (PrimalIsFeasible A b → ∀ a : ℝ, IsPrimalLowerBound A b c a →
      ∃ y : Fin m → ℝ, SystemD A b c y a) := by sorry

end ModernConvex.LPDuality
