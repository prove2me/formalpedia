-- Prove2me | Theorems.Thm_GomoryGroup_Rel_group_problem_periodic
-- name    : GomoryGroup.Rel.group_problem_periodic
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T08:29:18.475159+00:00
-- url     : https://prove2.me/theorems/81bb53ae-4d69-4f48-9771-5597b33ce3b6
-- title:
--   proof of THEOREM 1, p. 263 — φ(b + α_i) = φ(b): the group problem (4) is m-periodic in b
-- statement:
--   Let $B$ be an integer $m\times m$ matrix with columns $\alpha_1,\dots,\alpha_m$, $N$ an integer $m\times n$ matrix, $c_B\in\mathbb R^m$, $c_N\in\mathbb R^n$ and $b\in\mathbb Z^m$. For every $i=1,\dots,m$, the group problem (4) with right-hand side $b+\alpha_i$ has exactly the same feasible solutions $y\in\mathbb N^n$ as the one with right-hand side $b$, and hence the same set of objective values:
--   $$\{y: b+\alpha_i-Ny\in\mathfrak L_B\}=\{y: b-Ny\in\mathfrak L_B\},\qquad \text{so}\qquad \varphi(b+\alpha_i)=\varphi(b).$$
--
--   This is the periodicity of $\varphi^B$ and $y^B$ asserted in THEOREM 1: both depend only on the class of $b$ modulo the lattice $\mathfrak L_B$.
--
--   **Formalization Note** Column $j$ of $N$ is the paper's $\alpha_{m+1+j}$; the relative costs are $c^*_{m+1+j}$. No standing hypothesis is needed for this statement, so none is assumed.
-- source:
--   Gomory, On the relation between integer and noninteger solutions to linear programs, Proc. Natl. Acad. Sci. USA 53 (1965), p. 263, first line (proof of THEOREM 1)

import Mathlib
import Definitions.Def_GomoryGroup_Rel_Setting

namespace GomoryGroup.Rel

open Matrix

theorem group_problem_periodic {m n : ℕ} (B : Matrix (Fin m) (Fin m) ℤ)
    (N : Matrix (Fin m) (Fin n) ℤ) (cB : Fin m → ℝ) (cN : Fin n → ℝ) (b : Fin m → ℤ) :
    ∀ i : Fin m,
      (∀ y : Fin n → ℕ, IsGroupFeasible B N (b + fun r => B r i) y ↔ IsGroupFeasible B N b y) ∧
        groupValues B N cB cN (b + fun r => B r i) = groupValues B N cB cN b := by sorry

end GomoryGroup.Rel
