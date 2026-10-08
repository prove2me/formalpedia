-- Prove2me | Theorems.Thm_InertialAVD_StrongCvx_thm_3_4_last_display
-- name    : InertialAVD.StrongCvx.thm_3_4_last_display
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T23:12:15.590617+00:00
-- url     : https://prove2.me/theorems/9676d4a7-e588-44e4-98e3-546982555b3a
-- title:
--   Proof of Theorem 3.4, last display — for t ≥ t₁, ‖ẋ(t)‖² ≤ [4(1 + √(α/(α − 3)))² E^{2(α−3)/3}_{2α/3}(t₁)] t^{−2α/3}
-- statement:
--   Under the hypotheses of (26) ($\Phi$ continuously differentiable and strongly convex with constant $\mu>0$, $\alpha>3$, $x$ a solution of $\ddot x+\frac\alpha t\dot x+\nabla\Phi(x)=0$ on $[t_0,+\infty[$ with $t_0>0$, $x^*\in\operatorname{argmin}\Phi$, $t_1=\max\{t_0,\sqrt{p\lambda/\mu}\}$ with $p=\frac23(\alpha-3)$, $\lambda=\frac23\alpha$), for every $t\ge t_1$,
--   $$\|\dot x(t)\|^2\le\bigg[4\Big(1+\sqrt{\frac{\alpha}{\alpha-3}}\Big)^2\,\mathcal E^{\frac23(\alpha-3)}_{\frac23\alpha}(t_1)\bigg]\,t^{-\frac23\alpha}.$$
--
--   This is the explicit form of the third rate in (25), for the velocity.
--
--   **Formalization Note** $\dot x$ is the velocity component `v` of the solution; $t^{-2\alpha/3}$ is a real power of $t>0$.
-- source:
--   Attouch, Chbani, Peypouquet, Redont, Fast convergence of inertial dynamics and algorithms with asymptotic vanishing damping, Optimization Online preprint 5179 (Oct. 2015), p. 12, §3.3, proof of Theorem 3.4, last display

import Mathlib
import Definitions.Def_InertialAVD_StrongCvx_Setting

open InnerProductSpace Filter Topology Asymptotics

namespace InertialAVD.StrongCvx

theorem thm_3_4_last_display {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (Φ : H → ℝ) (hΦ : ContDiff ℝ 1 Φ) (μ : ℝ) (hsc : IsStronglyConvex Φ μ)
    (α t₀ : ℝ) (hα : 3 < α) (x v : ℝ → H) (hsol : InertialAVD.Traj.IsSolution Φ α t₀ x v)
    (xstar : H) (hmin : ∀ y, Φ xstar ≤ Φ y) :
    ∀ t, t1 t₀ α μ ≤ t →
      ‖v t‖ ^ 2 ≤ 4 * (1 + Real.sqrt (α / (α - 3))) ^ 2
          * energyP Φ x v xstar (2 / 3 * α) (2 / 3 * (α - 3)) (t1 t₀ α μ)
          * t ^ (-(2 / 3) * α) := by sorry

end InertialAVD.StrongCvx
