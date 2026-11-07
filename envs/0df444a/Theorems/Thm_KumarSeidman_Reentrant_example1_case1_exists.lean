-- Prove2me | Theorems.Thm_KumarSeidman_Reentrant_example1_case1_exists
-- name    : KumarSeidman.Reentrant.example1_case1_exists
-- status  : Proved
-- author  : @tianyipeng
-- created : 2026-11-06T17:23:23.291214+00:00
-- url     : https://prove2.me/theorems/e7621dc1-8748-44e2-9cbb-80168d15d96c
-- title:
--   Example 1, Case 1, pp. 291–292 — existence of clearing trajectories from a large initial backlog
-- statement:
--   Consider the re-entrant line of Example 1. One part type arrives at rate $1$ and visits machine 1, machine 2, machine 2 and machine 1, through buffers $1,2,3,4$. The processing times satisfy
--   $$\tau_2+\tau_4>1,\qquad \tau_1+\tau_4<1,\qquad \tau_2+\tau_3<1,$$
--   and the set-up times $\delta_1,\dots,\delta_4$ are positive. The initial state is $x(0)=(\xi,0,0,0)$, with machine 1 set up for buffer 4 and machine 2 set up for buffer 3.
--
--   **Claim.** There is $\xi_0$ such that for every $\xi>0$ with $\xi\ge\xi_0$, a trajectory of the fluid model under a clearing policy starts from this initial state.
--
--   This is the existence half of Case 1. It makes the instability statement `example1_case1_all_unbounded` non-vacuous. The paper exhibits the trajectory through its stage computation, which repeats with backlog $\xi\mapsto\lambda\xi+\beta$.
-- source:
--   Kumar & Seidman, Dynamic Instabilities and Stabilization Methods in Distributed Real-Time Scheduling of Manufacturing Systems, IEEE Trans. Automat. Control 35(3), 1990, pp. 291–292, §III Example 1, Case 1 (the trajectory described in the stage computation)

import Mathlib
import Definitions.Def_KumarSeidman_Reentrant_System
import Definitions.Def_KumarSeidman_Reentrant_Trajectory
import Definitions.Def_KumarSeidman_Reentrant_Clearing
import Definitions.Def_KumarSeidman_Reentrant_Example1

namespace KumarSeidman.Reentrant

/-- **Example 1, Case 1, existence** (Kumar–Seidman 1990, §III, pp. 291–292). With (3)–(5) and
positive set-up times, for all sufficiently large backlogs `ξ` a clearing trajectory starting at
`x(0) = (ξ, 0, 0, 0)` (machine 1 set up for buffer 4, machine 2 for buffer 3) exists. -/
theorem example1_case1_exists (τ : Fin 4 → ℝ) (hτ : ∀ k, 0 < τ k)
    (h3 : 1 < τ 1 + τ 3) (h4 : τ 0 + τ 3 < 1) (h5 : τ 1 + τ 2 < 1)
    (δ : Fin 4 → ℝ) (hδ : ∀ k, 0 < δ k) :
    ∃ ξ₀ : ℝ, ∀ ξ : ℝ, 0 < ξ → ξ₀ ≤ ξ →
      ∃ T : Trajectory (ex1 τ hτ δ (fun k => (hδ k).le)),
        IsClearing (ex1 τ hτ δ (fun k => (hδ k).le)) T ∧ Ex1Initial T ξ := by sorry

end KumarSeidman.Reentrant
