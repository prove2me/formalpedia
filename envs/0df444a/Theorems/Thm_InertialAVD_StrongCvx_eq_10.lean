-- Prove2me | Theorems.Thm_InertialAVD_StrongCvx_eq_10
-- name    : InertialAVD.StrongCvx.eq_10
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T23:12:11.131603+00:00
-- url     : https://prove2.me/theorems/0e378813-729d-4824-a3df-b12c2c8e2ae0
-- title:
--   (10) — the derivative of the anchored energy E^p_λ along a solution of (1)
-- statement:
--   Let $\mathcal H$ be a real Hilbert space, $\Phi:\mathcal H\to\mathbb R$ a continuously differentiable convex function, $\alpha>0$, and $x:[t_0,+\infty[\to\mathcal H$ (with $t_0>0$) a solution of $\ddot x(t)+\frac{\alpha}{t}\dot x(t)+\nabla\Phi(x(t))=0$. Let $x^*\in\operatorname{argmin}\Phi$, $\lambda\ge0$, $p\ge0$, and let $\mathcal E^p_\lambda(t)=t^p\big(t^2(\Phi(x(t))-\min\Phi)+\frac12\|\lambda(x(t)-x^*)+t\dot x(t)\|^2\big)$. Then for every $t\ge t_0$, writing $x=x(t)$ and $\dot x=\dot x(t)$,
--   $$\begin{aligned}\frac{d}{dt}\mathcal E^p_\lambda(t)={}&(p+2)t^{p+1}(\Phi(x)-\min\Phi)-\lambda t^{p+1}\langle x-x^*,\nabla\Phi(x)\rangle-\lambda(\alpha-\lambda-1-p)t^p\langle x-x^*,\dot x\rangle\\&+\frac{\lambda^2p}{2}t^{p-1}\|x-x^*\|^2-\Big(\alpha-\lambda-1-\frac p2\Big)t^{p+1}\|\dot x\|^2.\end{aligned}$$
--
--   This identity is the starting point of every Lyapunov estimate built on $\mathcal E^p_\lambda$; for strongly convex $\Phi$ it is combined with the strong convexity inequality to obtain the rate of Theorem 3.4.
--
--   **Formalization Note** The derivative is the derivative within $[t_0,+\infty[$ (a right derivative at $t=t_0$), and $\min\Phi$ is written $\Phi(x^*)$.
-- source:
--   Attouch, Chbani, Peypouquet, Redont, Fast convergence of inertial dynamics and algorithms with asymptotic vanishing damping, Optimization Online preprint 5179 (Oct. 2015), p. 5, (10)

import Mathlib
import Definitions.Def_InertialAVD_StrongCvx_Setting

open InnerProductSpace Filter Topology Asymptotics

namespace InertialAVD.StrongCvx

theorem eq_10 {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (Φ : H → ℝ) (hΦ : ContDiff ℝ 1 Φ) (hconv : ConvexOn ℝ Set.univ Φ)
    (α t₀ : ℝ) (hα : 0 < α) (x v : ℝ → H) (hsol : InertialAVD.Traj.IsSolution Φ α t₀ x v)
    (xstar : H) (hmin : ∀ y, Φ xstar ≤ Φ y) (lam p : ℝ) (hlam : 0 ≤ lam) (hp : 0 ≤ p) :
    ∀ t ∈ Set.Ici t₀, HasDerivWithinAt (energyP Φ x v xstar lam p)
      ((p + 2) * t ^ (p + 1) * (Φ (x t) - Φ xstar)
        - lam * t ^ (p + 1) * ⟪x t - xstar, gradient Φ (x t)⟫_ℝ
        - lam * (α - lam - 1 - p) * t ^ p * ⟪x t - xstar, v t⟫_ℝ
        + lam ^ 2 * p / 2 * t ^ (p - 1) * ‖x t - xstar‖ ^ 2
        - (α - lam - 1 - p / 2) * t ^ (p + 1) * ‖v t‖ ^ 2) (Set.Ici t₀) t := by sorry

end InertialAVD.StrongCvx
