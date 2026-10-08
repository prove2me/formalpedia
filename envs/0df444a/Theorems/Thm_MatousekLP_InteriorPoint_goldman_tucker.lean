-- Prove2me | Theorems.Thm_MatousekLP_InteriorPoint_goldman_tucker
-- name    : MatousekLP.InteriorPoint.goldman_tucker
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-03T11:44:42.948864+00:00
-- url     : https://prove2.me/theorems/ff3dd9de-47df-4fbf-a850-6f0a806f5684
-- title:
--   Lemma 7.2.2 — the Goldman–Tucker system solves or refutes the LP
-- statement:
--   Let $A$ be a real $m\times n$ matrix, $b\in\mathbb{R}^m$, $c\in\mathbb{R}^n$, and consider the linear program (7.7), maximize $c^{T}x$ subject to $Ax\le b$, $x\ge 0$, with dual minimize $b^{T}y$ subject to $A^{T}y\ge c$, $y\ge 0$. The Goldman–Tucker system (GTS) is
--
--   $$Ax-\tau b\le 0,\qquad -A^{T}y+\tau c\le 0,\qquad b^{T}y-c^{T}x\le 0,\qquad x,y\ge 0,\ \tau\ge 0,$$
--
--   and $\rho=\rho(x,y)=c^{T}x-b^{T}y$. Then:
--
--   1. no solution $(x,y,\tau)$ of (GTS) has both $\tau\neq 0$ and $\rho\neq 0$;
--   2. exactly one of the following holds: (GTS) has a solution with $\tau>0$, or (GTS) has a solution with $\rho>0$;
--   3. for every solution $(x,y,\tau)$ of (GTS) with $\tau>0$, $\frac1\tau x$ is an optimal solution of (7.7) and $\frac1\tau y$ is an optimal solution of its dual;
--   4. if $(x,y,\tau)$ is a solution of (GTS) with $\rho>0$, then (7.7) is infeasible or unbounded.
--
--   The homogeneous system (GTS) thus encodes, in a single feasibility problem, both the optimal solutions of (7.7) and a certificate that no optimum exists.
--
--   **Formalization Note** Indices are `Fin n` and `Fin m`. Optimality of $x$ (resp. $y$) is stated as feasibility together with $c^{T}x'\le c^{T}x$ for all feasible $x'$ (resp. $b^{T}y\le b^{T}y'$ for all dual feasible $y'$); unboundedness means that for every real $M$ some feasible $x$ has $c^{T}x>M$. "Exactly one" is `Xor`.
-- source:
--   Matoušek & Gärtner, Understanding and Using Linear Programming, Springer 2007, §7.2, p. 126, Lemma 7.2.2 (with (7.7) and (GTS) p. 126)

import Mathlib
import Definitions.Def_MatousekLP_InteriorPoint_SelfDual

namespace MatousekLP.InteriorPoint

open Matrix

/-- Lemma 7.2.2 (Matoušek & Gärtner, p. 126). For the linear program (7.7)
`maximize cᵀx subject to Ax ≤ b, x ≥ 0` and its Goldman–Tucker system (GTS), with
`ρ = cᵀx − bᵀy`:
1. no solution of (GTS) has both `τ` and `ρ` nonzero;
2. exactly one of the following occurs: (GTS) has a solution with `τ > 0`, or (GTS) has a
   solution with `ρ > 0`;
3. for every solution with `τ > 0`, `(1/τ)x` is an optimal solution of (7.7) and `(1/τ)y` is an
   optimal solution of its dual `minimize bᵀy subject to Aᵀy ≥ c, y ≥ 0`;
4. if (GTS) has a solution with `ρ > 0`, then (7.7) is infeasible or unbounded. -/
theorem goldman_tucker {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ)
    (c : Fin n → ℝ) :
    (∀ (x : Fin n → ℝ) (y : Fin m → ℝ) (τ : ℝ), IsGTSSolution A b c x y τ →
        τ = 0 ∨ gtsSlack b c x y = 0) ∧
    Xor (∃ (x : Fin n → ℝ) (y : Fin m → ℝ) (τ : ℝ), IsGTSSolution A b c x y τ ∧ 0 < τ)
      (∃ (x : Fin n → ℝ) (y : Fin m → ℝ) (τ : ℝ),
        IsGTSSolution A b c x y τ ∧ 0 < gtsSlack b c x y) ∧
    (∀ (x : Fin n → ℝ) (y : Fin m → ℝ) (τ : ℝ), IsGTSSolution A b c x y τ → 0 < τ →
        IsIneqOptimal A b c (τ⁻¹ • x) ∧ IsIneqDualOptimal A b c (τ⁻¹ • y)) ∧
    (∀ (x : Fin n → ℝ) (y : Fin m → ℝ) (τ : ℝ), IsGTSSolution A b c x y τ →
        0 < gtsSlack b c x y →
        (¬ ∃ x' : Fin n → ℝ, IsIneqFeasible A b x') ∨ IsIneqUnbounded A b c) := by sorry

end MatousekLP.InteriorPoint
