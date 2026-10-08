-- Prove2me | Theorems.Thm_InertialAVD_StrongCvx_eq_26
-- name    : InertialAVD.StrongCvx.eq_26
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T23:12:28.246992+00:00
-- url     : https://prove2.me/theorems/4b259eae-71c2-4bbb-85f6-b100192a5d21
-- title:
--   (26) — for t ≥ t₁, E^p_λ(t) ≤ E^p_λ(t₁) + (λp/4)t^p‖x(t) − x*‖² ≤ E^p_λ(t₁) + (λp/(2µ))t^p(Φ(x(t)) − min Φ)
-- statement:
--   Let $\mathcal H$ be a real Hilbert space, $\Phi:\mathcal H\to\mathbb R$ continuously differentiable and strongly convex with constant $\mu>0$, $\alpha>3$, $x:[t_0,+\infty[\to\mathcal H$ ($t_0>0$) a solution of $\ddot x+\frac\alpha t\dot x+\nabla\Phi(x)=0$, and $x^*\in\operatorname{argmin}\Phi$. Fix
--   $$p=\tfrac23(\alpha-3),\qquad\lambda=\tfrac23\alpha,\qquad t_1=\max\Big\{t_0,\sqrt{\tfrac{p\lambda}{\mu}}\Big\}.$$
--   Then for every $t\ge t_1$,
--   $$\mathcal E^p_\lambda(t)\le\mathcal E^p_\lambda(t_1)+\frac{\lambda p}{4}t^p\|x(t)-x^*\|^2\le\mathcal E^p_\lambda(t_1)+\frac{\lambda p}{2\mu}t^p\big(\Phi(x(t))-\min\Phi\big).\tag{26}$$
--
--   This is the integrated form of the differential inequality for $\mathcal E^p_\lambda$; it bounds the energy by its value at $t_1$ plus a term that is absorbed in (27).
--
--   **Formalization Note** $\min\Phi$ is written $\Phi(x^*)$; both inequalities of the chain are stated, for $t\ge t_1$ only.
-- source:
--   Attouch, Chbani, Peypouquet, Redont, Fast convergence of inertial dynamics and algorithms with asymptotic vanishing damping, Optimization Online preprint 5179 (Oct. 2015), p. 11, (26) (proof of Theorem 3.4)

import Mathlib
import Definitions.Def_InertialAVD_StrongCvx_Setting

open InnerProductSpace Filter Topology Asymptotics

namespace InertialAVD.StrongCvx

theorem eq_26 {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (Φ : H → ℝ) (hΦ : ContDiff ℝ 1 Φ) (μ : ℝ) (hsc : IsStronglyConvex Φ μ)
    (α t₀ : ℝ) (hα : 3 < α) (x v : ℝ → H) (hsol : InertialAVD.Traj.IsSolution Φ α t₀ x v)
    (xstar : H) (hmin : ∀ y, Φ xstar ≤ Φ y) :
    ∀ t, t1 t₀ α μ ≤ t →
      energyP Φ x v xstar (lam α) (pExp α) t
          ≤ energyP Φ x v xstar (lam α) (pExp α) (t1 t₀ α μ)
            + lam α * pExp α / 4 * t ^ pExp α * ‖x t - xstar‖ ^ 2 ∧
      energyP Φ x v xstar (lam α) (pExp α) (t1 t₀ α μ)
            + lam α * pExp α / 4 * t ^ pExp α * ‖x t - xstar‖ ^ 2
          ≤ energyP Φ x v xstar (lam α) (pExp α) (t1 t₀ α μ)
            + lam α * pExp α / (2 * μ) * t ^ pExp α * (Φ (x t) - Φ xstar) := by sorry

end InertialAVD.StrongCvx
