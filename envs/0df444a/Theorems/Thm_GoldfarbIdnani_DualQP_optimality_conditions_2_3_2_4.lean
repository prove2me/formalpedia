-- Prove2me | Theorems.Thm_GoldfarbIdnani_DualQP_optimality_conditions_2_3_2_4
-- name    : GoldfarbIdnani.DualQP.optimality_conditions_2_3_2_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T04:14:51.355513+00:00
-- url     : https://prove2.me/theorems/44e93db2-9b95-41dc-8c52-d71e37d51ef1
-- title:
--   Optimality conditions (2.3)–(2.4): $\bar x$ solves $P(A)$ iff $N^*g(\bar x) \ge 0$ and $Hg(\bar x) = 0$
-- statement:
--   Consider the quadratic program (1.1) with objective $f(x) = a^{\mathsf T}x + \tfrac12x^{\mathsf T}Gx$, $G$ symmetric positive definite, and constraints $s_i(x) = n_i^{\mathsf T}x - b_i \ge 0$. Let $A$ be a set of constraint indices with linearly independent normals, let $N^*$ and $H$ be the operators (2.1)–(2.2) for $A$, and let $\bar x$ lie on the manifold $\mathcal M = \{x : n_i^{\mathsf T}x = b_i,\ i \in A\}$. Then $\bar x$ is the optimal solution of the subproblem $P(A)$ (minimize $f$ subject to $s_i(x) \ge 0$, $i \in A$) if and only if
--
--   $$
--   u(\bar x) \equiv N^*g(\bar x) \ge 0 \quad (2.3) \qquad\text{and}\qquad Hg(\bar x) = 0, \quad (2.4)
--   $$
--
--   where $g(x) = Gx + a$ is the gradient of $f$.
--
--   This is the characterization behind the algorithm's tests: it turns the S-pair property "$x$ solves $P(A)$" into the two linear conditions maintained along the solution path.
--
--   **Formalization Note.** The paper derives (2.3)–(2.4) from the multiplier form $g(\bar x) = Nu(\bar x)$, $u(\bar x) \ge 0$, and states that they are "sufficient as well as necessary"; the Lean statement is that equivalence. The vector $N^*g(\bar x)$ is indexed by constraint indices, and the condition $\ge 0$ is required on the entries in $A$.
-- source:
--   Goldfarb and Idnani, A numerically stable dual method for solving strictly convex quadratic programs, Math. Programming 27 (1983), p. 5, Section 2, Eqs. (2.3)–(2.4)

import Mathlib
import Definitions.Def_GoldfarbIdnani_DualQP_QP

namespace GoldfarbIdnani.DualQP

open Matrix

theorem optimality_conditions_2_3_2_4 {n m : ℕ} (a : Fin n → ℝ)
    (G : Matrix (Fin n) (Fin n) ℝ) (C : Matrix (Fin n) (Fin m) ℝ) (b : Fin m → ℝ)
    (A : Finset (Fin m)) (xbar : Fin n → ℝ)
    (hG : G.PosDef) (hA : LinIndep C A) (hM : ∀ i ∈ A, slack C b xbar i = 0) :
    IsOptimalFor a G C b A xbar ↔
      ((∀ i ∈ A, 0 ≤ multVec G C A (grad a G xbar) i) ∧
        Hmat G C A *ᵥ grad a G xbar = 0) := by sorry

end GoldfarbIdnani.DualQP
