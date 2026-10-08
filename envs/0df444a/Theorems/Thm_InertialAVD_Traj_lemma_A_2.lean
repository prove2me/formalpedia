-- Prove2me | Theorems.Thm_InertialAVD_Traj_lemma_A_2
-- name    : InertialAVD.Traj.lemma_A_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T22:07:35.161466+00:00
-- url     : https://prove2.me/theorems/e846504c-9834-46d0-a506-77d5f32abf07
-- title:
--   Lemma A.2 (Opial, continuous form) — if $\lim\|x(t)-z\|$ exists for $z\in S$ and weak limit points lie in $S$, then $x(t)\rightharpoonup\bar x\in S$
-- statement:
--   Let $\mathcal H$ be a real Hilbert space, $S\subseteq\mathcal H$ a nonempty set, and $x:[0,+\infty)\to\mathcal H$. Assume that
--
--   1. for every $z\in S$, $\lim_{t\to\infty}\|x(t)-z\|$ exists;
--   2. every weak sequential limit point of $x(t)$, as $t\to\infty$, belongs to $S$.
--
--   Then there is $\bar x\in S$ such that
--   $$x(t)\rightharpoonup\bar x\quad\text{weakly as }t\to\infty.$$
--
--   This is the continuous-time form of Opial's lemma; it reduces the weak convergence of a trajectory to the convergence of its distances to a target set together with the location of its weak limit points.
--
--   **Formalization Note** $x$ is a map $\mathbb R\to\mathcal H$ and all limits are along $t\to+\infty$, so its values on bounded times play no role (the domain $[0,+\infty)$ of the page is immaterial). A weak sequential limit point is the weak limit of $x(s_n)$ for some times $s_n\to+\infty$. Completeness of $\mathcal H$ is assumed.
-- source:
--   Attouch, Chbani, Peypouquet, Redont, Fast convergence of inertial dynamics and algorithms with asymptotic vanishing damping, Optimization Online preprint 5179 (Oct. 2015), p. 24, Lemma A.2

import Mathlib
import Definitions.Def_InertialAVD_Traj_Setting

open Filter Topology

namespace InertialAVD.Traj

theorem lemma_A_2 {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (S : Set H) (hS : S.Nonempty) (x : ℝ → H)
    (h_i : ∀ z ∈ S, ∃ ℓ : ℝ, Tendsto (fun t => ‖x t - z‖) atTop (𝓝 ℓ))
    (h_ii : ∀ p : H, IsWeakLimitPoint x p → p ∈ S) :
    ∃ xbar ∈ S, WeakTendstoAtTop x xbar := by sorry

end InertialAVD.Traj
