-- Prove2me | Theorems.Thm_HryniewiczCriterion_ellipsoid_axis_prime_orbit_period
-- name    : HryniewiczCriterion.ellipsoid_axis_prime_orbit_period
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-07T16:15:17.539216+00:00
-- url     : https://prove2.me/theorems/62f19866-05f1-4fa0-aa9b-3a0a21524d9c
-- title:
--   A prime orbit on the axis $z_2=0$ of an ellipsoid has period $\pi r_1^2$
-- statement:
--   Let $r_1>0$, let $H(x)=\frac{q_1^2+p_1^2}{r_1^2}+\frac{q_2^2+p_2^2}{r_2^2}$, and let $P=(x,T)$ be a prime (simply covered) periodic orbit of $X_H$ on $\{H=1\}$ whose image lies in the axis $\{q_2=p_2=0\}$. Then $x(0)$ lies on the circle $q_1^2+p_1^2=r_1^2$, and the minimal period is
--   $$T=\pi r_1^2.$$
--   Proof idea: on the axis $z_1(t)=e^{2it/r_1^2}z_1(0)$ with $|z_1(0)|=r_1$. So $x(T)=x(0)$ forces $2T/r_1^2\in2\pi\mathbb Z_{>0}$, and primality excludes the multiples $k\ge2$.
-- source:
--   Hryniewicz, Systems of global surfaces of section for dynamically convex Reeb flows on the 3-sphere, J. Symplectic Geom. 12 (2014), https://arxiv.org/abs/1105.2077, p. 3 (ellipsoid example after Theorem 1.7); the period $\pi r_1^2$ is the action of the short/long axis orbit

import Definitions.Def_HryniewiczCriterion_Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

namespace HryniewiczCriterion

theorem ellipsoid_axis_prime_orbit_period {r₁ r₂ : ℝ} (h₁ : 0 < r₁)
    (P : PeriodicOrbit (fun x : R4 => (x 0 ^ 2 + x 1 ^ 2) / r₁ ^ 2 + (x 2 ^ 2 + x 3 ^ 2) / r₂ ^ 2)) (hP : P.IsPrime)
    (hax : P.image ⊆ {x | x 2 = 0 ∧ x 3 = 0}) :
    P.T = Real.pi * r₁ ^ 2 ∧ P.x 0 0 ^ 2 + P.x 0 1 ^ 2 = r₁ ^ 2 := by sorry

end HryniewiczCriterion
