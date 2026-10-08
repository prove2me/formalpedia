-- Prove2me | Theorems.Thm_InertialAVD_Traj_lemma_2_1
-- name    : InertialAVD.Traj.lemma_2_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T22:07:28.040847+00:00
-- url     : https://prove2.me/theorems/ac8de511-3d08-4d5b-8669-144b0fc91d52
-- title:
--   Lemma 2.1 — along a solution of (1), $\dot W(t)=-\frac{\alpha}{t}\|\dot x(t)\|^2$; $W$ is nonincreasing with a limit in $\mathbb R\cup\{-\infty\}$
-- statement:
--   Let $\mathcal H$ be a real Hilbert space, $\Phi:\mathcal H\to\mathbb R$ convex and continuously differentiable, $\alpha>0$, $t_0>0$, and let $x$ be a solution of
--   $$\ddot x(t)+\frac{\alpha}{t}\dot x(t)+\nabla\Phi(x(t))=0$$
--   on $[t_0,+\infty[$. Let $W(t)=\frac12\|\dot x(t)\|^2+\Phi(x(t))$ be the global energy. Then:
--
--   1. for each $t>t_0$, $W$ is differentiable at $t$ and
--   $$\dot W(t)=-\frac{\alpha}{t}\|\dot x(t)\|^2;$$
--   2. $W$ is nonincreasing on $[t_0,+\infty[$;
--   3. $W_\infty=\lim_{t\to+\infty}W(t)$ exists in $\mathbb R\cup\{-\infty\}$;
--   4. if $\Phi$ is bounded from below, $W_\infty$ is finite.
--
--   This energy dissipation identity is the basic estimate of the paper: it underlies the minimizing property of the trajectories (Theorem 2.3) through Lemma 2.2.
--
--   **Formalization Note** The limit in item 3 is taken in the extended reals `EReal`, with the value $+\infty$ excluded; in item 4 it is a real limit.
-- source:
--   Attouch, Chbani, Peypouquet, Redont, Fast convergence of inertial dynamics and algorithms with asymptotic vanishing damping, Optimization Online preprint 5179 (Oct. 2015), p. 3, Lemma 2.1

import Mathlib
import Definitions.Def_InertialAVD_Traj_Setting

open Filter Topology

namespace InertialAVD.Traj

theorem lemma_2_1 {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (Φ : H → ℝ) (hΦconv : ConvexOn ℝ Set.univ Φ) (hΦC1 : ContDiff ℝ 1 Φ)
    (α t₀ : ℝ) (hα : 0 < α) (x v : ℝ → H) (hsol : IsSolution Φ α t₀ x v) :
    (∀ t ∈ Set.Ioi t₀, HasDerivAt (energyW Φ x v) (-(α / t) * ‖v t‖ ^ 2) t) ∧
    AntitoneOn (energyW Φ x v) (Set.Ici t₀) ∧
    (∃ Winf : EReal, Winf ≠ ⊤ ∧
      Tendsto (fun t => ((energyW Φ x v t : ℝ) : EReal)) atTop (𝓝 Winf)) ∧
    (BddBelow (Set.range Φ) → ∃ Winf : ℝ, Tendsto (energyW Φ x v) atTop (𝓝 Winf)) := by sorry

end InertialAVD.Traj
