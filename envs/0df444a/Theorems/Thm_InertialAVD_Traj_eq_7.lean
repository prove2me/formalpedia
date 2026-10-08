-- Prove2me | Theorems.Thm_InertialAVD_Traj_eq_7
-- name    : InertialAVD.Traj.eq_7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T22:07:27.88397+00:00
-- url     : https://prove2.me/theorems/c082b0f9-4b19-45f2-ada7-5e2b2e31bef2
-- title:
--   (7) — $\ddot h_z(t)+\frac{\alpha}{t}\dot h_z(t)+\Phi(x(t))-\Phi(z)\le\|\dot x(t)\|^2$ along a solution of (1)
-- statement:
--   Let $\mathcal H$ be a real Hilbert space, $\Phi:\mathcal H\to\mathbb R$ convex and continuously differentiable, $\alpha>0$, $t_0>0$, and let $x$ be a solution of $\ddot x+\frac{\alpha}{t}\dot x+\nabla\Phi(x)=0$ on $[t_0,+\infty[$. Fix $z\in\mathcal H$ and let $h_z(t)=\frac12\|x(t)-z\|^2$.
--
--   Then for every $t\ge t_0$:
--   1. $h_z$ is differentiable at $t$ (within $[t_0,+\infty[$) with $\dot h_z(t)=\langle x(t)-z,\dot x(t)\rangle$;
--   2. the function $s\mapsto\langle x(s)-z,\dot x(s)\rangle$ is differentiable at $t$ (within $[t_0,+\infty[$), and its derivative $\ddot h_z(t)$ satisfies
--   $$\ddot h_z(t)+\frac{\alpha}{t}\dot h_z(t)+\Phi(x(t))-\Phi(z)\le\|\dot x(t)\|^2. \tag{7}$$
--
--   Inequality (7) is the differential inequality for the distance to an anchor point; with $z$ a minimizer it is the first hypothesis fed into the weak-convergence argument of Theorem 2.16, and it is integrated in Lemma 2.2.
--
--   **Formalization Note** Both derivatives are asserted, not assumed: the first identifies $\dot h_z$ as $\langle x-z,\dot x\rangle$ on the whole half-line, and the second asserts that this function is differentiable and that its derivative satisfies (7).
-- source:
--   Attouch, Chbani, Peypouquet, Redont, Fast convergence of inertial dynamics and algorithms with asymptotic vanishing damping, Optimization Online preprint 5179 (Oct. 2015), p. 3, §2.1, (5)–(7)

import Mathlib
import Definitions.Def_InertialAVD_Traj_Setting

namespace InertialAVD.Traj

theorem eq_7 {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (Φ : H → ℝ) (hΦconv : ConvexOn ℝ Set.univ Φ) (hΦC1 : ContDiff ℝ 1 Φ)
    (α t₀ : ℝ) (hα : 0 < α) (x v : ℝ → H) (hsol : IsSolution Φ α t₀ x v) (z : H) :
    ∀ t ∈ Set.Ici t₀,
      HasDerivWithinAt (anchorDist x z) (inner ℝ (x t - z) (v t)) (Set.Ici t₀) t ∧
      ∃ hdd : ℝ, HasDerivWithinAt (fun s => inner ℝ (x s - z) (v s)) hdd (Set.Ici t₀) t ∧
        hdd + (α / t) * inner ℝ (x t - z) (v t) + Φ (x t) - Φ z ≤ ‖v t‖ ^ 2 := by sorry

end InertialAVD.Traj
