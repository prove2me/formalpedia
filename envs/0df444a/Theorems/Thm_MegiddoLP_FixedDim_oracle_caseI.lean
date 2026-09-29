-- Prove2me | Theorems.Thm_MegiddoLP_FixedDim_oracle_caseI
-- name    : MegiddoLP.FixedDim.oracle_caseI
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-26T23:11:49.864552+00:00
-- url     : https://prove2.me/theorems/06ada43d-4352-46d1-a4a8-06bb363bce18
-- title:
--   Oracle, Case I: local improvement directions from $x^*$ and global optimality (corrected objective)
-- statement:
--   Consider the linear program minimize $c^Tx$ subject to $Ax\ge b$ in the variables $x_1,\dots,x_d$, and the hyperplane $\{x_d=0\}$. Let $x^*$ be an optimal solution relative to the hyperplane: $x^*$ is feasible, $x^*_d=0$, and $c^Tx^*\le c^Tx$ for every feasible $x$ with $x_d=0$. Let $I=\{i: a_i^Tx^*=b_i\}$ be the set of constraints tight at $x^*$. Consider the two auxiliary systems
--
--   $$(P_+)\quad z_d=1,\quad a_i^Tz\ge0\ (i\in I),\qquad\qquad (P_-)\quad z_d=-1,\quad a_i^Tz\ge0\ (i\in I),$$
--
--   and say that $(P_\pm)$ has a solution with **negative value** if some solution $z$ has $c^Tz<0$. Then:
--
--   1. there is a feasible $y$ with $y_d>0$ and $c^Ty<c^Tx^*$ if and only if $(P_+)$ has a solution with negative value;
--   2. there is a feasible $y$ with $y_d<0$ and $c^Ty<c^Tx^*$ if and only if $(P_-)$ has a solution with negative value;
--   3. $(P_+)$ and $(P_-)$ do not both have solutions with negative value;
--   4. if neither has, then $x^*$ is an optimal solution of the original program.
--
--   This tells the oracle on which side of $\{x_d=0\}$ the optimum lies, or that $x^*$ is already optimal, by solving problems in $d-1$ free variables.
--
--   **Formalization Note** (corrected) The page writes the auxiliary objective as $\sum_{j=1}^{d-1}c_jx_j$. The direction has $x_d=\pm1$, so its cost is $\sum_{j<d}c_jz_j\pm c_d$, and with the printed objective parts 1 and 2 fail whenever $c_d\ne0$. The Lean uses $c^Tz$, which includes the $\pm c_d$ term. The paper's $x_d$ is the last coordinate `Fin.last d` of `Fin (d + 1)`, so Lean's $d+1$ is the paper's $d$. The hypothesis on $x^*$ is optimality among feasible points of the hyperplane, not global optimality.
-- source:
--   Megiddo, Linear Programming in Linear Time When the Dimension Is Fixed, J. ACM 31(1) (1984) 114–127, §4, p. 124 (Case I)

import Mathlib
import Definitions.Def_Polyhedron

/-!
Megiddo, J. ACM 31 (1984), §4 p. 124, Case I of the oracle. The paper's `x_d` is the last
coordinate `Fin.last d` of `Fin (d + 1)`; the tested hyperplane is `{x_d = 0}`. The auxiliary
objective is `c ⬝ᵥ z` with `z_d = ±1`, i.e. the page's `Σ_{j<d} c_j z_j` corrected by the term
`± c_d`.
-/

open Matrix LinearOptimization

namespace MegiddoLP.FixedDim

/-- **Oracle, Case I.** Let `x*` be optimal for `minimize cᵀx` over the feasible points of
`Ax ≥ b` lying on `{x_d = 0}`, and let `I = {i | Aᵢ ⬝ᵥ x* = bᵢ}`. Then
1. some feasible `y` with `y_d > 0` has `cᵀy < cᵀx*` iff some `z` with `z_d = 1`,
   `Aᵢ ⬝ᵥ z ≥ 0` for `i ∈ I` has `cᵀz < 0`;
2. the same with `y_d < 0` and `z_d = -1`;
3. the two auxiliary systems of 1 and 2 do not both have a solution of negative value;
4. if neither does, `x*` is optimal for the original program. -/
theorem oracle_caseI {n d : ℕ} (A : Matrix (Fin n) (Fin (d + 1)) ℝ) (b : Fin n → ℝ)
    (c xs : Fin (d + 1) → ℝ)
    (hxs : IsLpOptimal c (polyhedron A b ∩ {x | x (Fin.last d) = 0}) xs) :
    ((∃ y ∈ polyhedron A b, 0 < y (Fin.last d) ∧ c ⬝ᵥ y < c ⬝ᵥ xs) ↔
      ∃ z : Fin (d + 1) → ℝ, z (Fin.last d) = 1 ∧
        (∀ i, A i ⬝ᵥ xs = b i → 0 ≤ A i ⬝ᵥ z) ∧ c ⬝ᵥ z < 0) ∧
    ((∃ y ∈ polyhedron A b, y (Fin.last d) < 0 ∧ c ⬝ᵥ y < c ⬝ᵥ xs) ↔
      ∃ z : Fin (d + 1) → ℝ, z (Fin.last d) = -1 ∧
        (∀ i, A i ⬝ᵥ xs = b i → 0 ≤ A i ⬝ᵥ z) ∧ c ⬝ᵥ z < 0) ∧
    ¬ ((∃ z : Fin (d + 1) → ℝ, z (Fin.last d) = 1 ∧
          (∀ i, A i ⬝ᵥ xs = b i → 0 ≤ A i ⬝ᵥ z) ∧ c ⬝ᵥ z < 0) ∧
       (∃ z : Fin (d + 1) → ℝ, z (Fin.last d) = -1 ∧
          (∀ i, A i ⬝ᵥ xs = b i → 0 ≤ A i ⬝ᵥ z) ∧ c ⬝ᵥ z < 0)) ∧
    ((¬ ∃ z : Fin (d + 1) → ℝ, z (Fin.last d) = 1 ∧
          (∀ i, A i ⬝ᵥ xs = b i → 0 ≤ A i ⬝ᵥ z) ∧ c ⬝ᵥ z < 0) →
     (¬ ∃ z : Fin (d + 1) → ℝ, z (Fin.last d) = -1 ∧
          (∀ i, A i ⬝ᵥ xs = b i → 0 ≤ A i ⬝ᵥ z) ∧ c ⬝ᵥ z < 0) →
     IsLpOptimal c (polyhedron A b) xs) := by sorry

end MegiddoLP.FixedDim
