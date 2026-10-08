-- Prove2me | Theorems.Thm_InertialAVD_StrongCvx_thm_3_4_first_display
-- name    : InertialAVD.StrongCvx.thm_3_4_first_display
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T23:12:43.091978+00:00
-- url     : https://prove2.me/theorems/cfd96942-713b-4469-9323-1b7b7646acf3
-- title:
--   Proof of Theorem 3.4, first display — for strongly convex Φ, the derivative of E^p_λ is bounded by a quadratic form in Φ(x) − min Φ, ⟨x − x*, ẋ⟩, ‖x − x*‖², ‖ẋ‖²
-- statement:
--   Let $\mathcal H$ be a real Hilbert space and $\Phi:\mathcal H\to\mathbb R$ continuously differentiable and strongly convex with constant $\mu>0$, i.e. $\Phi(y)\ge\Phi(x)+\langle\nabla\Phi(x),y-x\rangle+\frac\mu2\|x-y\|^2$ for all $x,y$. Let $\alpha>0$, let $x:[t_0,+\infty[\to\mathcal H$ ($t_0>0$) be a solution of $\ddot x+\frac\alpha t\dot x+\nabla\Phi(x)=0$, let $x^*\in\operatorname{argmin}\Phi$, and let $\lambda\ge0$, $p\ge0$. If $D$ is the derivative of $\mathcal E^p_\lambda$ at $t\ge t_0$, then, writing $x=x(t)$, $\dot x=\dot x(t)$,
--   $$\begin{aligned}D\le{}&(p+2-\lambda)t^{p+1}(\Phi(x)-\min\Phi)-\lambda(\alpha-\lambda-1-p)t^p\langle x-x^*,\dot x\rangle\\&-\frac\lambda2(\mu t^2-p\lambda)t^{p-1}\|x-x^*\|^2-\Big(\alpha-\lambda-1-\frac p2\Big)t^{p+1}\|\dot x\|^2.\end{aligned}$$
--
--   With the choice $p=\frac23(\alpha-3)$, $\lambda=\frac23\alpha$ the first and last coefficients vanish, which is how the proof of Theorem 3.4 proceeds.
--
--   **Formalization Note** The statement quantifies over every $D$ that is a derivative of $\mathcal E^p_\lambda$ within $[t_0,+\infty[$ at $t$ (such $D$ exists and is unique by (10)); $\min\Phi$ is written $\Phi(x^*)$.
-- source:
--   Attouch, Chbani, Peypouquet, Redont, Fast convergence of inertial dynamics and algorithms with asymptotic vanishing damping, Optimization Online preprint 5179 (Oct. 2015), p. 11, §3.3, proof of Theorem 3.4, first display

import Mathlib
import Definitions.Def_InertialAVD_StrongCvx_Setting

open InnerProductSpace Filter Topology Asymptotics

namespace InertialAVD.StrongCvx

theorem thm_3_4_first_display {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H]
    (Φ : H → ℝ) (hΦ : ContDiff ℝ 1 Φ) (μ : ℝ) (hsc : IsStronglyConvex Φ μ)
    (α t₀ : ℝ) (hα : 0 < α) (x v : ℝ → H) (hsol : InertialAVD.Traj.IsSolution Φ α t₀ x v)
    (xstar : H) (hmin : ∀ y, Φ xstar ≤ Φ y) (lam p : ℝ) (hlam : 0 ≤ lam) (hp : 0 ≤ p) :
    ∀ t ∈ Set.Ici t₀, ∀ D : ℝ,
      HasDerivWithinAt (energyP Φ x v xstar lam p) D (Set.Ici t₀) t →
      D ≤ (p + 2 - lam) * t ^ (p + 1) * (Φ (x t) - Φ xstar)
          - lam * (α - lam - 1 - p) * t ^ p * ⟪x t - xstar, v t⟫_ℝ
          - lam / 2 * (μ * t ^ 2 - p * lam) * t ^ (p - 1) * ‖x t - xstar‖ ^ 2
          - (α - lam - 1 - p / 2) * t ^ (p + 1) * ‖v t‖ ^ 2 := by sorry

end InertialAVD.StrongCvx
