-- Prove2me | Theorems.Thm_InertialAVD_Traj_remark_2_6
-- name    : InertialAVD.Traj.remark_2_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T22:07:43.929126+00:00
-- url     : https://prove2.me/theorems/7dc696a6-9db2-46a3-9c1b-857bfa477af2
-- title:
--   Remark 2.6 — $\frac{d}{dt}\mathcal E_{\lambda,\xi}\le(2-\lambda)t(\Phi(x)-\min\Phi)+(\xi-\lambda(\alpha-\lambda-1))\langle x-x^*,\dot x\rangle-(\alpha-\lambda-1)t\|\dot x\|^2$
-- statement:
--   Let $\mathcal H$ be a real Hilbert space, $\Phi:\mathcal H\to\mathbb R$ convex and continuously differentiable, $\alpha>0$, $t_0>0$, and let $x$ be a solution of $\ddot x+\frac{\alpha}{t}\dot x+\nabla\Phi(x)=0$ on $[t_0,+\infty[$. Let $x^*\in\operatorname{argmin}\Phi$, $\lambda\ge0$, and for $\xi\ge0$ let
--   $$\mathcal E_{\lambda,\xi}(t)=t^2(\Phi(x(t))-\min\Phi)+\tfrac12\|\lambda(x(t)-x^*)+t\dot x(t)\|^2+\tfrac{\xi}{2}\|x(t)-x^*\|^2.$$
--   Then:
--
--   1. for every $\xi\ge0$ and $t\ge t_0$, $\mathcal E_{\lambda,\xi}$ is differentiable at $t$ (within $[t_0,+\infty[$) and
--   $$\frac{d}{dt}\mathcal E_{\lambda,\xi}(t)\le(2-\lambda)\,t\,(\Phi(x)-\min\Phi)+(\xi-\lambda(\alpha-\lambda-1))\langle x-x^*,\dot x\rangle-(\alpha-\lambda-1)\,t\,\|\dot x\|^2;$$
--   2. with $\xi^*=\lambda(\alpha-\lambda-1)$ (when $\xi^*\ge0$), for every $t\ge t_0$,
--   $$\frac{d}{dt}\mathcal E_{\lambda,\xi^*}(t)\le(2-\lambda)\,t\,(\Phi(x)-\min\Phi)-(\alpha-\lambda-1)\,t\,\|\dot x\|^2;$$
--   3. if $\alpha\ge3$ and $2\le\lambda\le\alpha-1$, then $\mathcal E_{\lambda,\xi^*}$ is nonincreasing on $[t_0,+\infty[$.
--
--   Here $x$, $\dot x$ are evaluated at $t$ and $\min\Phi=\Phi(x^*)$. These Lyapunov inequalities drive the convergence analysis: $\lambda=\alpha-1$ gives the $O(1/t^2)$ rate, and $\lambda=2$ gives the integrability estimate of Theorem 2.14 ii).
--
--   **Formalization Note** The paper fixes $\xi\ge0$ for the whole of §2.3; item 2 is therefore stated under $\xi^*\ge0$, which holds automatically in the range of item 3.
-- source:
--   Attouch, Chbani, Peypouquet, Redont, Fast convergence of inertial dynamics and algorithms with asymptotic vanishing damping, Optimization Online preprint 5179 (Oct. 2015), p. 4, §2.3 (λ ≥ 0, ξ ≥ 0, x* ∈ argmin Φ) and p. 5, (9), Remark 2.6

import Mathlib
import Definitions.Def_InertialAVD_Traj_Setting

namespace InertialAVD.Traj

theorem remark_2_6 {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (Φ : H → ℝ) (hΦconv : ConvexOn ℝ Set.univ Φ) (hΦC1 : ContDiff ℝ 1 Φ)
    (α t₀ : ℝ) (hα : 0 < α) (x v : ℝ → H) (hsol : IsSolution Φ α t₀ x v)
    (xstar : H) (hxstar : ∀ y : H, Φ xstar ≤ Φ y) (lam : ℝ) (hlam : 0 ≤ lam) :
    (∀ ξ : ℝ, 0 ≤ ξ → ∀ t ∈ Set.Ici t₀, ∃ D : ℝ,
      HasDerivWithinAt (anchoredEnergy Φ x v lam ξ xstar) D (Set.Ici t₀) t ∧
      D ≤ (2 - lam) * t * (Φ (x t) - Φ xstar)
          + (ξ - lam * (α - lam - 1)) * inner ℝ (x t - xstar) (v t)
          - (α - lam - 1) * t * ‖v t‖ ^ 2) ∧
    (0 ≤ lam * (α - lam - 1) → ∀ t ∈ Set.Ici t₀, ∃ D : ℝ,
      HasDerivWithinAt (anchoredEnergy Φ x v lam (lam * (α - lam - 1)) xstar) D (Set.Ici t₀) t ∧
      D ≤ (2 - lam) * t * (Φ (x t) - Φ xstar) - (α - lam - 1) * t * ‖v t‖ ^ 2) ∧
    (3 ≤ α → 2 ≤ lam → lam ≤ α - 1 →
      AntitoneOn (anchoredEnergy Φ x v lam (lam * (α - lam - 1)) xstar) (Set.Ici t₀)) := by sorry

end InertialAVD.Traj
