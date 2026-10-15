-- Prove2me | Theorems.Thm_LPCommunity_LPRecovery_theorem_3
-- name    : LPCommunity.LPRecovery.theorem_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T06:48:12.495447+00:00
-- url     : https://prove2.me/theorems/534e2656-0e75-4bcc-b4db-d241e2bf4a99
-- title:
--   Theorem 3, pp. 9–10 (Mangasarian) — an LP optimum is unique iff Ax = 0, C_K x = 0, C_L x ≥ 0 has only x = 0
-- statement:
--   Consider the linear program
--   $$\min_x\ c^{\top}x \quad\text{s.t.}\quad Ax=b,\quad Cx\ge d,$$
--   where $c\in\mathbb R^N$, $b\in\mathbb R^m$, $d\in\mathbb R^k$, $A$ is an $m\times N$ matrix and $C$ a $k\times N$ matrix, and its dual
--   $$\max_{u,v}\ b^{\top}u+d^{\top}v\quad\text{s.t.}\quad A^{\top}u+C^{\top}v=c,\quad v\ge 0.$$
--   Let $\bar x$ be an optimal solution of the primal and $(\bar u,\bar v)$ an optimal solution of the dual. Write $C_i$ for the $i$-th row of $C$ and set
--   $$K=\{i:\ C_i\bar x=d_i,\ \bar v_i>0\},\qquad L=\{i:\ C_i\bar x=d_i,\ \bar v_i=0\}.$$
--   Then $\bar x$ is the unique optimal solution of the primal if and only if there is no $x\neq 0$ with
--   $$Ax=0,\qquad C_Kx=0,\qquad C_Lx\ge 0.$$
--
--   This is part (iv) of Theorem 2 of Mangasarian (1979), *Uniqueness of solution in linear programming*; the paper uses it to certify that the cut vector is the only optimum of (LP-P).
--
--   **Formalization Note** The paper writes $p$ for the cost vector and $n$ for the number of variables; here they are $c$ and $N$. Optimality of $\bar x$ is feasibility plus $c^\top\bar x\le c^\top x$ for every feasible $x$; optimality of $(\bar u,\bar v)$ is dual feasibility plus $b^\top u+d^\top v\le b^\top\bar u+d^\top\bar v$ for every dual-feasible $(u,v)$. Uniqueness is stated as "every feasible $x$ with $c^\top x\le c^\top\bar x$ equals $\bar x$". The criterion is posed for an arbitrary pair of optimal solutions, as on the page.
-- source:
--   Del Pia, Khajavirad, Kunisky, Linear Programming and Community Detection, arXiv:2006.03213v2, pp. 9–10, Theorem 3 (= Mangasarian, Uniqueness of solution in linear programming, Linear Algebra Appl. 25 (1979), Theorem 2 (iv))

import Mathlib

open Matrix

namespace LPCommunity.LPRecovery

theorem theorem_3 {N m k : ℕ} (A : Matrix (Fin m) (Fin N) ℝ) (C : Matrix (Fin k) (Fin N) ℝ)
    (c : Fin N → ℝ) (b : Fin m → ℝ) (d : Fin k → ℝ)
    (xbar : Fin N → ℝ) (hxfeas : A *ᵥ xbar = b ∧ ∀ i, d i ≤ (C *ᵥ xbar) i)
    (hxopt : ∀ x : Fin N → ℝ, A *ᵥ x = b → (∀ i, d i ≤ (C *ᵥ x) i) → c ⬝ᵥ xbar ≤ c ⬝ᵥ x)
    (ubar : Fin m → ℝ) (vbar : Fin k → ℝ)
    (hdfeas : Aᵀ *ᵥ ubar + Cᵀ *ᵥ vbar = c ∧ ∀ i, 0 ≤ vbar i)
    (hdopt : ∀ (u : Fin m → ℝ) (v : Fin k → ℝ), Aᵀ *ᵥ u + Cᵀ *ᵥ v = c → (∀ i, 0 ≤ v i) →
      b ⬝ᵥ u + d ⬝ᵥ v ≤ b ⬝ᵥ ubar + d ⬝ᵥ vbar) :
    (∀ x : Fin N → ℝ, A *ᵥ x = b → (∀ i, d i ≤ (C *ᵥ x) i) → c ⬝ᵥ x ≤ c ⬝ᵥ xbar → x = xbar) ↔
      ¬ ∃ x : Fin N → ℝ, x ≠ 0 ∧ A *ᵥ x = 0 ∧
        (∀ i, (C *ᵥ xbar) i = d i → 0 < vbar i → (C *ᵥ x) i = 0) ∧
        (∀ i, (C *ᵥ xbar) i = d i → vbar i = 0 → 0 ≤ (C *ᵥ x) i) := by sorry

end LPCommunity.LPRecovery
