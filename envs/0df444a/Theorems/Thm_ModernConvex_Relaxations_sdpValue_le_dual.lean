-- Prove2me | Theorems.Thm_ModernConvex_Relaxations_sdpValue_le_dual
-- name    : ModernConvex.Relaxations.sdpValue_le_dual
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T10:09:27.299577+00:00
-- url     : https://prove2.me/theorems/b0890df3-9bad-430d-a8a5-d1f618f636f3
-- title:
--   Weak duality: a dual feasible point bounds the MAXCUT SDP value from above
-- statement:
--   **Weak duality for the Max-Cut SDP.** Let $a$ be a real matrix and $S$ the optimal value of $\max\{\tfrac14\sum_{i,j}a_{ij}(1-X_{ij}) : X\succeq0,\ X_{ii}=1\}$. For every vector $\lambda\in\mathbb R^n$ with $a+\operatorname{diag}\lambda\succeq0$,
--   $$S\;\le\;\frac14\Big(\sum_{i,j}a_{ij}+\sum_i\lambda_i\Big).$$
--
--   Proof. Let $X$ be feasible. Since $a+\operatorname{diag}\lambda$ and $X$ are both positive semidefinite, $\langle a+\operatorname{diag}\lambda, X\rangle=\operatorname{tr}\big((a+\operatorname{diag}\lambda)X\big)\ge0$. Expanding, using $X_{ii}=1$ and the symmetry of $X$, gives $\sum_{i,j}a_{ij}X_{ij}\ge-\sum_i\lambda_i$. Therefore
--   $$\tfrac14\sum_{i,j}a_{ij}(1-X_{ij})=\tfrac14\Big(\sum_{i,j}a_{ij}-\sum_{i,j}a_{ij}X_{ij}\Big)\le\tfrac14\Big(\sum_{i,j}a_{ij}+\sum_i\lambda_i\Big),$$
--   so the right-hand side is an upper bound for the objective on the feasible set, and hence dominates the least upper bound $S$.
--
--   This is the half of SDP duality that a solver certifies numerically: any rational $\lambda$ with $a+\operatorname{diag}\lambda\succeq0$ yields a rigorous upper bound by pure rational arithmetic. Together with the primal bound it pins $S$ once a pair $(X,\lambda)$ with small duality gap $\tfrac14\langle a+\operatorname{diag}\lambda,X\rangle$ is exhibited.
-- source:
--   Ben-Tal & Nemirovski, Lectures on Modern Convex Optimization, (4.3.15), p. 170; weak duality for the MAXCUT semidefinite relaxation, the certificate a numerical solver produces.

import Mathlib
import Definitions.Def_ModernConvex_Relaxations_SignRelaxations

open Matrix
open scoped BigOperators MatrixOrder

namespace ModernConvex.Relaxations

/-- **Weak duality: the dual bound.** For every `λ` with `a + diag λ ⪰ 0`, the optimal value
of the Max-Cut SDP is at most `(1/4)(Σ_{i,j} a_ij + Σ_i λ_i)`. -/
theorem sdpValue_le_dual {n : ℕ} {a : Matrix (Fin n) (Fin n) ℝ} {S : ℝ}
    (hS : IsMaxcutSDPValue a S) (lam : Fin n → ℝ)
    (hdual : (a + Matrix.diagonal lam).PosSemidef) :
    S ≤ (1 / 4) * ((∑ i, ∑ j, a i j) + ∑ i, lam i) := by sorry

end ModernConvex.Relaxations
