-- Prove2me | Theorems.Thm_MatousekLP_Duality_weak_duality
-- name    : MatousekLP.Duality.weak_duality
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-03T11:15:38.304694+00:00
-- url     : https://prove2.me/theorems/19bd3695-2351-46b1-9c52-6516a029acde
-- title:
--   Proposition 6.1.1 — weak duality for (P) and (D)
-- statement:
--   Consider the linear programs (P) maximize $c^{T}x$ subject to $Ax\le b$, $x\ge 0$, and (D) minimize $b^{T}y$ subject to $A^{T}y\ge c$, $y\ge 0$, with $A$ a real $m\times n$ matrix, $b\in\mathbb{R}^m$, $c\in\mathbb{R}^n$. Then:
--
--   1. for every feasible solution $x$ of (P) and every feasible solution $y$ of (D),
--   $$c^{T}x\le b^{T}y;$$
--   2. if (P) is unbounded, then (D) has no feasible solution;
--   3. if (D) is unbounded from below, then (P) has no feasible solution.
--
--   Every dual feasible solution thus certifies an upper bound on the objective of (P). This is the half of the duality theorem that rules out three of the nine combinations of feasible-bounded, unbounded and infeasible for (P) and (D).
--
--   **Formalization Note** Feasibility, unboundedness of (P) (arbitrarily large objective values) and unboundedness of (D) (arbitrarily small objective values) are the notions of the definition module `MatousekLP.Duality.PrimalDual`.
-- source:
--   Matoušek & Gärtner, Understanding and Using Linear Programming, Springer 2007, p. 83, Proposition 6.1.1

import Mathlib
import Definitions.Def_MatousekLP_Duality_PrimalDual

namespace MatousekLP.Duality

open Matrix

/-- Matoušek & Gärtner, Proposition 6.1.1 (p. 83), weak duality for (P) and (D):
for every feasible `x` of (P) and feasible `y` of (D), `cᵀx ≤ bᵀy`; in particular, if (P) is
unbounded then (D) is infeasible, and if (D) is unbounded (from below) then (P) is infeasible. -/
theorem weak_duality {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (c : Fin n → ℝ) :
    (∀ x y, IsPrimalFeasible A b x → IsDualFeasible A c y → c ⬝ᵥ x ≤ b ⬝ᵥ y) ∧
    (PrimalUnbounded A b c → ¬ ∃ y, IsDualFeasible A c y) ∧
    (DualUnbounded A b c → ¬ ∃ x, IsPrimalFeasible A b x) := by sorry

end MatousekLP.Duality
