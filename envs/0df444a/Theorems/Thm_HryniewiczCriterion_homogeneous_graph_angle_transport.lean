-- Prove2me | Theorems.Thm_HryniewiczCriterion_homogeneous_graph_angle_transport
-- name    : HryniewiczCriterion.homogeneous_graph_angle_transport
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-06T15:22:53.79188+00:00
-- url     : https://prove2.me/theorems/f880a9bf-1521-4b02-a828-1c90ceda0bb1
-- title:
--   Graph angle of the framed linearized flow equals twice the polar angle of the contact path
-- statement:
--   Let $K$ be a homogeneous convex model, $Q=(x,T)$ a periodic orbit of $X_K$ on $S=K^{-1}(1)$, $Z$ its normalized variational flow, $F$ the symplectic frame at $x(0)$ with columns $x$, $X_K/\omega_0(x,X_K)$, $Z_1$, $Z_2$, and $\varphi$ the contact-plane path. Then there are continuous angle functions $\theta$ on $[0,T]$ and $\alpha$ on $[0,1]$, both vanishing at $0$, such that
--   $$\det V\big(F^{-1}Z(t)F\big)=e^{i\theta(t)},\qquad \varphi(\tau)=R(\alpha(\tau))\,P(\tau)$$
--   with $P(\tau)$ symmetric positive definite and $R(a)$ the rotation by $a$, and
--   $$\theta(T)=2\,\alpha(1).$$
--   Here $V$ is the $4\times4$ graph unitary. This is the frame-change step of HWZ (3.38)–(3.41), where the linearized flow along the orbit is compared, through the contractible loop of frames $t\mapsto F(x(t))$, with the split flow $\operatorname{diag}(I_2,\varphi)$.
-- source:
--   Hofer–Wysocki–Zehnder, The dynamics on three-dimensional strictly convex energy surfaces, Ann. of Math. 148 (1998), https://doi.org/10.2307/120994, proof of Theorem 3.4, (3.36)–(3.41), p. 221 (contractible frame loop), with the frame of Hryniewicz, https://arxiv.org/html/1105.2077v5, Section 2.1.1, equations (4)–(5). Reduction lemma; not a verbatim numbered assertion.

import Definitions.Def_HryniewiczCriterion_GraphAngle

open HryniewiczCriterion
open scoped ContDiff

theorem HryniewiczCriterion.homogeneous_graph_angle_transport (K : R4 → ℝ) (hK : IsHomogeneousConvexModel K)
    (Q : PeriodicOrbit K) (Z : ℝ → (R4 →L[ℝ] R4)) (hZ : IsLinearizedFlow K Q.x Z) :
    ∃ θ α : ℝ → ℝ, IsDetAngleLift (fun t => graphUnitary4 (frameFlowMatrix K Q Z t)) Q.T θ ∧
      IsPolarAngleLift (linearizedXiPath K Q Z) α ∧ θ Q.T = 2 * α 1 := by sorry
