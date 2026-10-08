-- Prove2me | Theorems.Thm_InertialAVD_StrongCvx_theorem_3_4
-- name    : InertialAVD.StrongCvx.theorem_3_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T23:12:28.103248+00:00
-- url     : https://prove2.me/theorems/0bdfca4e-e93e-4bff-9aa3-f751d7ddbb7b
-- title:
--   Theorem 3.4 — for strongly convex Φ and α > 3, x(t) → x* strongly and Φ(x(t)) − min Φ, ‖x(t) − x*‖², ‖ẋ(t)‖² are O(t^{−2α/3})
-- statement:
--   Let $\mathcal H$ be a real Hilbert space and $\Phi:\mathcal H\to\mathbb R$ a continuously differentiable function that is strongly convex: for some $\mu>0$,
--   $$\Phi(y)\ge\Phi(x)+\langle\nabla\Phi(x),y-x\rangle+\frac\mu2\|x-y\|^2\qquad\text{for all }x,y\in\mathcal H.$$
--   Let $\alpha>3$, $t_0>0$, and let $x:[t_0,+\infty[\to\mathcal H$ be a solution of
--   $$\ddot x(t)+\frac{\alpha}{t}\dot x(t)+\nabla\Phi(x(t))=0.$$
--   Then $\Phi$ has a unique minimizer $x^*$, $x(t)$ converges strongly (in norm) to $x^*$ as $t\to+\infty$, and
--   $$\Phi(x(t))-\min\Phi=\mathcal O\big(t^{-\frac23\alpha}\big),\qquad\|x(t)-x^*\|^2=\mathcal O\big(t^{-\frac23\alpha}\big),\qquad\|\dot x(t)\|^2=\mathcal O\big(t^{-\frac23\alpha}\big)\tag{25}$$
--   as $t\to+\infty$.
--
--   For merely convex $\Phi$ the values converge at rate $\mathcal O(t^{-2})$; under strong convexity the rate improves without bound as $\alpha$ grows.
--
--   **Formalization Note** The existence and uniqueness of the minimizer are part of the conclusion, not hypotheses. $\mathcal O$ is `Asymptotics.IsBigO` along `atTop`; $\dot x$ is the velocity component `v` of the solution; $\min\Phi=\Phi(x^*)$; $t^{-2\alpha/3}$ is the real power.
-- source:
--   Attouch, Chbani, Peypouquet, Redont, Fast convergence of inertial dynamics and algorithms with asymptotic vanishing damping, Optimization Online preprint 5179 (Oct. 2015), p. 11, Theorem 3.4, (25)

import Mathlib
import Definitions.Def_InertialAVD_StrongCvx_Setting

open InnerProductSpace Filter Topology Asymptotics

namespace InertialAVD.StrongCvx

theorem theorem_3_4 {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (Φ : H → ℝ) (hΦ : ContDiff ℝ 1 Φ) (μ : ℝ) (hsc : IsStronglyConvex Φ μ)
    (α t₀ : ℝ) (hα : 3 < α) (x v : ℝ → H) (hsol : InertialAVD.Traj.IsSolution Φ α t₀ x v) :
    ∃ xstar : H, (∀ y, Φ xstar ≤ Φ y) ∧ (∀ z, (∀ y, Φ z ≤ Φ y) → z = xstar) ∧
      Tendsto x atTop (𝓝 xstar) ∧
      (fun t => Φ (x t) - Φ xstar) =O[atTop] (fun t : ℝ => t ^ (-(2 / 3) * α)) ∧
      (fun t => ‖x t - xstar‖ ^ 2) =O[atTop] (fun t : ℝ => t ^ (-(2 / 3) * α)) ∧
      (fun t => ‖v t‖ ^ 2) =O[atTop] (fun t : ℝ => t ^ (-(2 / 3) * α)) := by sorry

end InertialAVD.StrongCvx
