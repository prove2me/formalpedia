-- Prove2me | Theorems.Thm_ModernConvex_Relaxations_ellipsoid_step_conditions
-- name    : ModernConvex.Relaxations.ellipsoid_step_conditions
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T10:26:24.267214+00:00
-- url     : https://prove2.me/theorems/2bb81ff0-4793-4cd7-9824-b4497257cca5
-- title:
--   The SDP dual oracle satisfies both step conditions of the ellipsoid run
-- statement:
--   **The separation oracle discharges both step conditions of the ellipsoid method on the Max-Cut SDP dual.**
--
--   Let $a$ be a real symmetric matrix, $X=\{\lambda : a+\operatorname{diag}\lambda\succeq0\}$ the dual spectrahedron, and $f(\lambda)=\tfrac14\big(\sum_{i,j}a_{ij}+\sum_i\lambda_i\big)$ the affine dual objective. For every centre $c\in\mathbb R^n$:
--
--   1. if $c\in X$, then the constant vector $p=(\tfrac14,\dots,\tfrac14)$ is a subgradient of $f$ at $c$ relative to $X$, i.e. $f(c)+p\cdot(x-c)\le f(x)$ for all $x\in X$ — in fact with equality, since $f$ is affine with gradient $p$;
--   2. if $c\notin X$, then there is $w\neq0$ with $(x-c)\cdot w\le0$ for all $x\in X$, namely $w_i=-v_i^2$ where $v$ is a negative direction of the slack $a+\operatorname{diag}c$.
--
--   These are precisely the two problem-dependent clauses of a run of the ellipsoid method in the sense of `ConvexOptAlg.Ellipsoid.IsEllipsoidRun` (Bubeck, arXiv:1405.4980, §2.2): at each step the oracle either certifies membership and returns a subgradient, or returns a separating vector. The remaining clauses — the explicit centre and matrix updates — are pure linear algebra independent of the problem, so the whole run on the dual spectrahedron can be assembled from this node alone.
-- source:
--   Bubeck, Convex Optimization: Algorithms and Complexity, arXiv:1405.4980v2, §2.2 pp. 249-250 (IsEllipsoidRun); Ben-Tal & Nemirovski, (4.3.15), p. 170 (the MAXCUT dual).

import Mathlib
import Definitions.Def_ModernConvex_Relaxations_SignRelaxations
import Definitions.Def_LinearOptimization_Subgradient

open Matrix
open scoped BigOperators

namespace ModernConvex.Relaxations

/-- **The two step conditions of the ellipsoid run, discharged by the oracle.** At every centre
`c`, either `c` is dual feasible and the constant vector `(1/4, …, 1/4)` is a subgradient of the
affine dual objective on the spectrahedron, or `c` is infeasible and there is a nonzero
separating vector for the spectrahedron through `c`. -/
theorem ellipsoid_step_conditions {n : ℕ} {a : Matrix (Fin n) (Fin n) ℝ} (ha : a.IsHermitian)
    (c : Fin n → ℝ) :
    (c ∈ {lam : Fin n → ℝ | (a + Matrix.diagonal lam).PosSemidef} →
        LinearOptimization.IsSubgradientOn (fun lam : Fin n → ℝ => (1 / 4) * ((∑ i, ∑ j, a i j) + ∑ i, lam i)) {lam : Fin n → ℝ | (a + Matrix.diagonal lam).PosSemidef}
          (fun _ => (1 / 4 : ℝ)) c) ∧
      (c ∉ {lam : Fin n → ℝ | (a + Matrix.diagonal lam).PosSemidef} →
        ∃ w : Fin n → ℝ, w ≠ 0 ∧ ∀ x ∈ {lam : Fin n → ℝ | (a + Matrix.diagonal lam).PosSemidef}, (x - c) ⬝ᵥ w ≤ 0) := by sorry

end ModernConvex.Relaxations
