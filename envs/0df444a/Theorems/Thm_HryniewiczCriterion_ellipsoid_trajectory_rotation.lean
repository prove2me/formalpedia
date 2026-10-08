-- Prove2me | Theorems.Thm_HryniewiczCriterion_ellipsoid_trajectory_rotation
-- name    : HryniewiczCriterion.ellipsoid_trajectory_rotation
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-07T16:15:19.668908+00:00
-- url     : https://prove2.me/theorems/853baa0c-da63-4511-a309-a0b8b9818b98
-- title:
--   Trajectories on an ellipsoid rotate both complex planes
-- statement:
--   Let $H(x)=\frac{q_1^2+p_1^2}{r_1^2}+\frac{q_2^2+p_2^2}{r_2^2}$ on $\mathbb R^4$ with coordinates $(q_1,p_1,q_2,p_2)$, and let $y$ be a trajectory of $X_H$ on $\{H=1\}$ (convention $\omega_0(X_H,\cdot)=-dH$). Then, writing $z_j=q_j+ip_j$,
--   $$z_1(t)=e^{2it/r_1^2}\,z_1(0),\qquad z_2(t)=e^{2it/r_2^2}\,z_2(0).$$
--   The real and imaginary parts are written out in the Lean statement. No positivity of $r_j$ is needed; for $r_j=0$ both sides degenerate consistently with Lean's $x/0=0$.
-- source:
--   Hryniewicz, Systems of global surfaces of section for dynamically convex Reeb flows on the 3-sphere, J. Symplectic Geom. 12 (2014), https://arxiv.org/abs/1105.2077, p. 3 (ellipsoid example after Theorem 1.7)

import Definitions.Def_HryniewiczCriterion_Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

namespace HryniewiczCriterion

theorem ellipsoid_trajectory_rotation {r₁ r₂ : ℝ} {y : ℝ → R4}
    (hy : IsTrajectory (fun x : R4 => (x 0 ^ 2 + x 1 ^ 2) / r₁ ^ 2 + (x 2 ^ 2 + x 3 ^ 2) / r₂ ^ 2) y) (t : ℝ) :
    (y t 0 = Real.cos (2 / r₁ ^ 2 * t) * y 0 0 - Real.sin (2 / r₁ ^ 2 * t) * y 0 1 ∧
      y t 1 = Real.sin (2 / r₁ ^ 2 * t) * y 0 0 + Real.cos (2 / r₁ ^ 2 * t) * y 0 1) ∧
    (y t 2 = Real.cos (2 / r₂ ^ 2 * t) * y 0 2 - Real.sin (2 / r₂ ^ 2 * t) * y 0 3 ∧
      y t 3 = Real.sin (2 / r₂ ^ 2 * t) * y 0 2 + Real.cos (2 / r₂ ^ 2 * t) * y 0 3) := by sorry

end HryniewiczCriterion
