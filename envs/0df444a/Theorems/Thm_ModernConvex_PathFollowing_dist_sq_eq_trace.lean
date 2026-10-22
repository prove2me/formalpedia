-- Prove2me | Theorems.Thm_ModernConvex_PathFollowing_dist_sq_eq_trace
-- name    : ModernConvex.PathFollowing.dist_sq_eq_trace
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-20T15:34:44.943904+00:00
-- url     : https://prove2.me/theorems/035391ca-1f71-4f18-9305-91d63dec61c3
-- title:
--   Eq. (6.4.11) — the SDP distance to the central path in trace form
-- statement:
--   Let $X, S$ be real symmetric positive definite $k \times k$ matrices and $t > 0$. Write $X^{1/2}$ for the positive semidefinite square root of $X$ and $\|\cdot\|_2$ for the Frobenius norm. Then
--
--   $$\operatorname{Tr}\big(X(tS - X^{-1})X(tS - X^{-1})\big) = \|tX^{1/2}SX^{1/2} - I\|_2^2.$$
--
--   In the book the left-hand side is how the squared distance $\operatorname{dist}^2((X,S), Z_*(t)) = \langle[\nabla^2 S_k(X)]^{-1}(tS + \nabla S_k(X)), tS + \nabla S_k(X)\rangle_F$ from $(X, S)$ to the point of the primal-dual central path comes out for the barrier $S_k(X) = -\ln\operatorname{Det}X$; the right-hand side is the form in which the neighbourhood $\mathcal N_\kappa$ of the path is used.
--
--   **Formalization Note** Only the second equality of (6.4.11), the one between the two explicit expressions, is stated; the first is the definition of the distance through the Hessian of the barrier, and the mission defines the distance directly by the right-hand side.
-- source:
--   Ben-Tal & Nemirovski, Lectures on Modern Convex Optimization, SIAM 2001, p. 395, Eq. (6.4.11)

import Mathlib
import Definitions.Def_ModernConvex_PathFollowing_SDP

open Matrix
open scoped MatrixOrder

namespace ModernConvex.PathFollowing

/-- Ben-Tal–Nemirovski, (6.4.11), p. 395: in the SDP case, for `t > 0` and positive definite
`X, S`, `Tr(X(tS − X⁻¹)X(tS − X⁻¹)) = ‖tX^{1/2}SX^{1/2} − I‖₂²`, `X^{1/2}` the positive
semidefinite square root of `X`, `‖·‖₂` the Frobenius norm. -/
theorem dist_sq_eq_trace {k : ℕ} (t : ℝ) (ht : 0 < t) (X S : Matrix (Fin k) (Fin k) ℝ)
    (hX : X.PosDef) (hS : S.PosDef) :
    (X * (t • S - X⁻¹) * X * (t • S - X⁻¹)).trace = centralPathDist t X S ^ 2 := by sorry

end ModernConvex.PathFollowing
