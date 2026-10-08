-- Prove2me | Theorems.Thm_MatousekLP_Integrality_tu_integral_optimal
-- name    : MatousekLP.Integrality.tu_integral_optimal
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-03T10:28:49.515425+00:00
-- url     : https://prove2.me/theorems/d31d2c27-2b0b-422a-a132-5c9d1f010721
-- title:
--   Lemma 8.2.4 — a TU linear program with integral right-hand side has an integral optimum
-- statement:
--   Consider a linear program with $n$ nonnegative variables and $m$ inequalities of the form
--   $$
--   \text{maximize } c^T x \quad \text{subject to } Ax \le b,\ x \ge 0,
--   $$
--   where $A$ is a real $m \times n$ matrix, $c \in \mathbb{R}^n$ and $b \in \mathbb{Z}^m$. If $A$ is totally unimodular and the linear program has an optimal solution, then it also has an integral optimal solution $x^* \in \mathbb{Z}^n$.
--
--   This lemma is what makes integer programs with a totally unimodular constraint matrix solvable by linear programming: the integrality constraints can be dropped without changing the optimum. The objective vector $c$ need not be integral.
--
--   **Formalization Note** "Optimal solution" is a feasible point whose objective value is at least that of every feasible point. The integral optimal solution is given as a vector $z \in \mathbb{Z}^n$ whose real image is optimal.
-- source:
--   Matoušek & Gärtner, Understanding and Using Linear Programming, Springer 2007, p. 145, Lemma 8.2.4

import Mathlib
import Definitions.Def_MatousekLP_Integrality_InequalityLP

namespace MatousekLP.Integrality

theorem tu_integral_optimal {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℤ)
    (c : Fin n → ℝ) (hA : A.IsTotallyUnimodular)
    (hopt : ∃ x : Fin n → ℝ, IsOptimalIneq A (fun i => (b i : ℝ)) c x) :
    ∃ z : Fin n → ℤ, IsOptimalIneq A (fun i => (b i : ℝ)) c (fun j => (z j : ℝ)) := by sorry

end MatousekLP.Integrality
