-- Prove2me | Theorems.Thm_InertialAVD_Traj_theorem_2_3_i
-- name    : InertialAVD.Traj.theorem_2_3_i
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T22:07:27.599327+00:00
-- url     : https://prove2.me/theorems/f2ee8878-44ff-4d3f-9c6e-1150b9f5c759
-- title:
--   Theorem 2.3 i) — $\lim W(t)=\lim\Phi(x(t))=\inf\Phi\in\mathbb R\cup\{-\infty\}$ for every solution of (1), $\alpha>0$
-- statement:
--   Let $\mathcal H$ be a real Hilbert space, $\Phi:\mathcal H\to\mathbb R$ convex and continuously differentiable, $\alpha>0$, $t_0>0$, and let $x$ be a solution of $\ddot x+\frac{\alpha}{t}\dot x+\nabla\Phi(x)=0$ on $[t_0,+\infty[$, with global energy $W(t)=\frac12\|\dot x(t)\|^2+\Phi(x(t))$. Then
--   $$W_\infty=\lim_{t\to+\infty}W(t)=\lim_{t\to+\infty}\Phi(x(t))=\inf\Phi\in\mathbb R\cup\{-\infty\}.$$
--
--   No minimizer is assumed and $\Phi$ need not be bounded from below: the trajectories of (1) minimize $\Phi$ in complete generality. Part ii) (weak limit points are minimizers) follows from this.
--
--   **Formalization Note** Both limits are taken in the extended reals `EReal`, and $\inf\Phi$ is the infimum of $\Phi(y)$ over $y\in\mathcal H$ in `EReal`, which is $-\infty$ when $\Phi$ is unbounded below.
-- source:
--   Attouch, Chbani, Peypouquet, Redont, Fast convergence of inertial dynamics and algorithms with asymptotic vanishing damping, Optimization Online preprint 5179 (Oct. 2015), p. 3, Theorem 2.3 i)

import Mathlib
import Definitions.Def_InertialAVD_Traj_Setting

open Filter Topology

namespace InertialAVD.Traj

theorem theorem_2_3_i {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (Φ : H → ℝ) (hΦconv : ConvexOn ℝ Set.univ Φ) (hΦC1 : ContDiff ℝ 1 Φ)
    (α t₀ : ℝ) (hα : 0 < α) (x v : ℝ → H) (hsol : IsSolution Φ α t₀ x v) :
    Tendsto (fun t => ((energyW Φ x v t : ℝ) : EReal)) atTop (𝓝 (⨅ y : H, ((Φ y : ℝ) : EReal))) ∧
    Tendsto (fun t => ((Φ (x t) : ℝ) : EReal)) atTop (𝓝 (⨅ y : H, ((Φ y : ℝ) : EReal))) := by sorry

end InertialAVD.Traj
