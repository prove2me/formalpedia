-- Prove2me | Theorems.Thm_InertialAVD_StrongCvx_eq_28
-- name    : InertialAVD.StrongCvx.eq_28
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T23:12:31.157432+00:00
-- url     : https://prove2.me/theorems/55c240df-2fb4-4b6b-8611-a04e4266f89d
-- title:
--   (28) — for t ≥ t₁, ‖x(t) − x*‖² ≤ (2/µ)(Φ(x(t)) − min Φ) ≤ [(4/µ)E^p_λ(t₁)]t^{−p−2} = [(4/µ)E^{2(α−3)/3}_{2α/3}(t₁)]t^{−2α/3}
-- statement:
--   Under the hypotheses of (26) ($\Phi$ continuously differentiable and strongly convex with constant $\mu>0$, $\alpha>3$, $x$ a solution of $\ddot x+\frac\alpha t\dot x+\nabla\Phi(x)=0$ on $[t_0,+\infty[$ with $t_0>0$, $x^*\in\operatorname{argmin}\Phi$, $p=\frac23(\alpha-3)$, $\lambda=\frac23\alpha$, $t_1=\max\{t_0,\sqrt{p\lambda/\mu}\}$), for every $t\ge t_1$,
--   $$\|x(t)-x^*\|^2\le\frac2\mu\big(\Phi(x(t))-\min\Phi\big)\le\Big[\frac4\mu\mathcal E^p_\lambda(t_1)\Big]t^{-p-2}=\Big[\frac4\mu\mathcal E^{\frac23(\alpha-3)}_{\frac23\alpha}(t_1)\Big]t^{-\frac23\alpha}.\tag{28}$$
--
--   This is the explicit form of the second rate in (25), and gives strong convergence of $x(t)$ to $x^*$.
--
--   **Formalization Note** All three links of the chain are stated, for $t\ge t_1$. $\min\Phi$ is written $\Phi(x^*)$.
-- source:
--   Attouch, Chbani, Peypouquet, Redont, Fast convergence of inertial dynamics and algorithms with asymptotic vanishing damping, Optimization Online preprint 5179 (Oct. 2015), p. 11, (28) (proof of Theorem 3.4)

import Mathlib
import Definitions.Def_InertialAVD_StrongCvx_Setting

open InnerProductSpace Filter Topology Asymptotics

namespace InertialAVD.StrongCvx

theorem eq_28 {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (Φ : H → ℝ) (hΦ : ContDiff ℝ 1 Φ) (μ : ℝ) (hsc : IsStronglyConvex Φ μ)
    (α t₀ : ℝ) (hα : 3 < α) (x v : ℝ → H) (hsol : InertialAVD.Traj.IsSolution Φ α t₀ x v)
    (xstar : H) (hmin : ∀ y, Φ xstar ≤ Φ y) :
    ∀ t, t1 t₀ α μ ≤ t →
      ‖x t - xstar‖ ^ 2 ≤ 2 / μ * (Φ (x t) - Φ xstar) ∧
      2 / μ * (Φ (x t) - Φ xstar)
          ≤ 4 / μ * energyP Φ x v xstar (lam α) (pExp α) (t1 t₀ α μ) * t ^ (-pExp α - 2) ∧
      4 / μ * energyP Φ x v xstar (lam α) (pExp α) (t1 t₀ α μ) * t ^ (-pExp α - 2)
          = 4 / μ * energyP Φ x v xstar (2 / 3 * α) (2 / 3 * (α - 3)) (t1 t₀ α μ)
              * t ^ (-(2 / 3) * α) := by sorry

end InertialAVD.StrongCvx
