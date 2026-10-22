-- Prove2me | Theorems.Thm_ModernConvex_LPDuality_dual_lower_bounds
-- name    : ModernConvex.LPDuality.dual_lower_bounds
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-20T15:32:29.10878+00:00
-- url     : https://prove2.me/theorems/16a0a65f-6a6b-484a-ae19-4a9f96577b10
-- title:
--   Proposition 1.3.3 — dual objective values bound $c^*$ from below, and for feasible (LP) every $a \le c^*$ is attained by some dual feasible $y$
-- statement:
--   Consider the LP program $\text{(LP)}\ \min_x\{c^Tx \mid Ax \ge b\}$ with optimal value $c^*$, and its dual $\text{(LP}^*)\ \max_y\{b^Ty \mid A^Ty = c,\ y \ge 0\}$. Then:
--
--   1. whenever $y$ is a feasible solution of (LP$^*$), the value $b^Ty$ of the dual objective is a lower bound on $c^*$: $c^Tx \ge b^Ty$ for every $x$ with $Ax \ge b$;
--   2. if (LP) is feasible, then for every $a \le c^*$ there is a feasible solution $y$ of (LP$^*$) with
--   $$b^Ty \ge a.$$
--
--   The proposition is the bridge from the theorem on the alternative to the LP duality theorem: it says that the dual problem captures all lower bounds on the primal optimal value.
--
--   **Formalization Note** "$a \le c^*$" is stated as "$a$ is a lower bound on the optimal value", $\forall x,\ Ax \ge b \Rightarrow a \le c^Tx$, which is the same thing whether $c^*$ is finite or $-\infty$, and never assigns $c^*$ a junk real value.
-- source:
--   Ben-Tal & Nemirovski, Lectures on Modern Convex Optimization, SIAM 2001, p. 17, Proposition 1.3.3

import Mathlib
import Definitions.Def_ModernConvex_LPDuality_LinearProgram

open Matrix

namespace ModernConvex.LPDuality

/-- Ben-Tal–Nemirovski, Proposition 1.3.3, p. 17: `bᵀy` is a lower bound on `c*` for every
feasible `y` of `(LP∗)`; if `(LP)` is feasible, every `a ≤ c*` is dominated by some `bᵀy`. -/
theorem dual_lower_bounds {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ)
    (c : Fin n → ℝ) :
    (∀ y : Fin m → ℝ, DualFeasible A c y → IsPrimalLowerBound A b c (b ⬝ᵥ y)) ∧
    (PrimalIsFeasible A b → ∀ a : ℝ, IsPrimalLowerBound A b c a →
      ∃ y : Fin m → ℝ, DualFeasible A c y ∧ a ≤ b ⬝ᵥ y) := by sorry

end ModernConvex.LPDuality
