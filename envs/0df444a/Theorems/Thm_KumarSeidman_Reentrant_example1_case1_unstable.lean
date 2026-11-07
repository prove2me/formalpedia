-- Prove2me | Theorems.Thm_KumarSeidman_Reentrant_example1_case1_unstable
-- name    : KumarSeidman.Reentrant.example1_case1_unstable
-- status  : Proved
-- author  : @tianyipeng
-- created : 2026-11-06T16:16:08.643799+00:00
-- url     : https://prove2.me/theorems/0909bb93-bd12-4f2e-8287-4aa24e7c54fa
-- title:
--   Example 1, Case 1, pp. 291–292 — with positive set-up times, clearing is unstable on the re-entrant line for large initial backlog
-- statement:
--   Consider the re-entrant line of Example 1: one part type arriving at rate $1$ visits machine 1, machine 2, machine 2 and machine 1, through buffers $1,2,3,4$, with processing times $\tau_1,\dots,\tau_4>0$ satisfying
--   $$\tau_2+\tau_4>1,\qquad \tau_1+\tau_4<1,\qquad \tau_2+\tau_3<1,$$
--   and with **positive set-up times** $\delta_1,\dots,\delta_4>0$ ($\delta_k$ is the time to set a machine up for buffer $k$).
--
--   **Case 1.** There is $\xi_0$ such that for every $\xi>0$ with $\xi\ge\xi_0$, a clearing trajectory starting from $x(0)=(\xi,0,0,0)$, with machine 1 set up for buffer 4 and machine 2 set up for buffer 3, exists. Moreover, along every such trajectory
--   $$\sup_{0\le t<\infty} x_1(t)=+\infty .$$
--
--   This is the first half (Case 1) of the mission's goal theorem `example1_clearing_unstable`. The paper proves it through the cycle map $x(T_0)=(\xi,0,0,0)\mapsto x(T_1)=(\lambda\xi+\beta,0,0,0)$ with $\lambda=\tau_4/(1-\tau_2)>1$. Unboundedness is formalized as: for every $C$ there is $t\ge 0$ with $x_1(t)>C$. The existence half makes the universal half non-vacuous.
-- source:
--   Kumar & Seidman, Dynamic Instabilities and Stabilization Methods in Distributed Real-Time Scheduling of Manufacturing Systems, IEEE Trans. Automat. Control 35(3), 1990, pp. 291–292, §III Example 1, Case 1

import Mathlib
import Definitions.Def_KumarSeidman_Reentrant_System
import Definitions.Def_KumarSeidman_Reentrant_Trajectory
import Definitions.Def_KumarSeidman_Reentrant_Clearing
import Definitions.Def_KumarSeidman_Reentrant_Example1

namespace KumarSeidman.Reentrant

/-- **Example 1, Case 1** (Kumar–Seidman 1990, §III, pp. 291–292). On the re-entrant line of
Example 1 with processing times `τ₁, …, τ₄ > 0` (Lean `τ 0, …, τ 3`) satisfying (3)
`τ₂ + τ₄ > 1`, (4) `τ₁ + τ₄ < 1` and (5) `τ₂ + τ₃ < 1`, and positive set-up times
`δ₁, …, δ₄ > 0`, there is `ξ₀` such that for every `ξ > 0` with `ξ ≥ ξ₀` a clearing trajectory
from `x(0) = (ξ, 0, 0, 0)` (machine 1 set up for buffer 4, machine 2 for buffer 3) exists, and
along every such trajectory the level `x₁` of buffer 1 is unbounded on `[0, ∞)`. -/
theorem example1_case1_unstable (τ : Fin 4 → ℝ) (hτ : ∀ k, 0 < τ k)
    (h3 : 1 < τ 1 + τ 3) (h4 : τ 0 + τ 3 < 1) (h5 : τ 1 + τ 2 < 1)
    (δ : Fin 4 → ℝ) (hδ : ∀ k, 0 < δ k) :
    ∃ ξ₀ : ℝ, ∀ ξ : ℝ, 0 < ξ → ξ₀ ≤ ξ →
      (∃ T : Trajectory (ex1 τ hτ δ (fun k => (hδ k).le)),
        IsClearing (ex1 τ hτ δ (fun k => (hδ k).le)) T ∧ Ex1Initial T ξ) ∧
      ∀ T : Trajectory (ex1 τ hτ δ (fun k => (hδ k).le)),
        IsClearing (ex1 τ hτ δ (fun k => (hδ k).le)) T → Ex1Initial T ξ →
          ∀ C : ℝ, ∃ t : ℝ, 0 ≤ t ∧ C < T.x (ex1Buf 0) t := by sorry

end KumarSeidman.Reentrant
