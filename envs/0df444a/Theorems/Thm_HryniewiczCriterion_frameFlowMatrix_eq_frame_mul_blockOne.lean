-- Prove2me | Theorems.Thm_HryniewiczCriterion_frameFlowMatrix_eq_frame_mul_blockOne
-- name    : HryniewiczCriterion.frameFlowMatrix_eq_frame_mul_blockOne
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-06T20:03:14.661473+00:00
-- url     : https://prove2.me/theorems/8978cc04-019e-4a81-8b81-0572e8dd8453
-- title:
--   Frame-flow factorization of the linearized flow at every time
-- statement:
--   Let $K$ be a homogeneous convex model on $\mathbb{R}^4$, let $Q=(x,T)$ be a periodic orbit of $X_K$ on $K^{-1}(1)$, and let $Z(t)$ be the linearized flow along $x$. For $y\neq0$, let $F(y)$ be the frame with columns
--   $$y,\quad X_K(y)/\omega_0(y,X_K(y)),\quad Z_1(y),\quad Z_2(y).$$
--   Let $\varphi$ be the contact-plane path of $Q$, i.e. the linearized Reeb flow on $\xi$ in the frame $Z_1,Z_2$. Then for every $t\in\mathbb{R}$,
--   $$F(x(0))^{-1}\,Z(t)\,F(x(0))=F(x(0))^{-1}F(x(t))\;\mathrm{diag}\bigl(I_2,\ \varphi(t/T)\bigr).$$
--
--   So the linearized flow of a $2$-homogeneous Hamiltonian splits, at every time, into a frame-change loop $F(x(0))^{-1}F(x(t))$ and the contact-plane path. At $t=T$ the loop is trivial, and this becomes `homogeneous_frame_flow_split`.
-- source:
--   Hofer–Wysocki–Zehnder, The dynamics on three-dimensional strictly convex energy surfaces, Ann. of Math. 148 (1998), https://doi.org/10.2307/120994, (3.34)–(3.36), p. 220; extends the platform theorem `HryniewiczCriterion.homogeneous_frame_flow_split` from $t=T$ to all $t$.

import Definitions.Def_HryniewiczCriterion_GraphAngle

open HryniewiczCriterion
open scoped ContDiff

theorem HryniewiczCriterion.frameFlowMatrix_eq_frame_mul_blockOne (K : R4 → ℝ)
    (hK : IsHomogeneousConvexModel K) (Q : PeriodicOrbit K) (Z : ℝ → (R4 →L[ℝ] R4))
    (hZ : IsLinearizedFlow K Q.x Z) (t : ℝ) :
    frameFlowMatrix K Q Z t = (homogFrame K (Q.x 0))⁻¹ * homogFrame K (Q.x t) *
      blockOne (linearizedXiPath K Q Z (t / Q.T)) := by sorry
