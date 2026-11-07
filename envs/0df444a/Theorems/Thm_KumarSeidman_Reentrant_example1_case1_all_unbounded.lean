-- Prove2me | Theorems.Thm_KumarSeidman_Reentrant_example1_case1_all_unbounded
-- name    : KumarSeidman.Reentrant.example1_case1_all_unbounded
-- status  : Proved
-- author  : @tianyipeng
-- created : 2026-11-06T17:23:23.832987+00:00
-- url     : https://prove2.me/theorems/1c992e76-53df-47d7-8510-6030ae9a07e4
-- title:
--   Example 1, Case 1, pp. 291–292 — every clearing trajectory from a large backlog has unbounded buffer 1
-- statement:
--   Consider the re-entrant line of Example 1. One part type arrives at rate $1$ and visits machine 1, machine 2, machine 2 and machine 1, through buffers $1,2,3,4$. The processing times satisfy
--   $$\tau_2+\tau_4>1,\qquad \tau_1+\tau_4<1,\qquad \tau_2+\tau_3<1,$$
--   and the set-up times $\delta_1,\dots,\delta_4$ are positive. The initial state is $x(0)=(\xi,0,0,0)$, with machine 1 set up for buffer 4 and machine 2 set up for buffer 3.
--
--   **Claim.** There is $\xi_0$ such that for every $\xi>0$ with $\xi\ge\xi_0$, every clearing trajectory from this initial state satisfies
--   $$\sup_{0\le t<\infty}x_1(t)=+\infty .$$
--
--   The reason is the paper's cycle map: the state $(\xi,0,0,0)$ returns as $(\lambda\xi+\beta,0,0,0)$ with $\lambda=\tau_4/(1-\tau_2)>1$.
--
--   **Formalization Note.** Unboundedness is stated as: for every $C$ there is $t\ge0$ with $x_1(t)>C$.
-- source:
--   Kumar & Seidman, Dynamic Instabilities and Stabilization Methods in Distributed Real-Time Scheduling of Manufacturing Systems, IEEE Trans. Automat. Control 35(3), 1990, pp. 291–292, §III Example 1, Case 1

import Mathlib
import Definitions.Def_KumarSeidman_Reentrant_System
import Definitions.Def_KumarSeidman_Reentrant_Trajectory
import Definitions.Def_KumarSeidman_Reentrant_Clearing
import Definitions.Def_KumarSeidman_Reentrant_Example1

namespace KumarSeidman.Reentrant

/-- **Example 1, Case 1, instability** (Kumar–Seidman 1990, §III, pp. 291–292). With (3)–(5) and
positive set-up times, for all sufficiently large backlogs `ξ`, along every clearing trajectory
starting at `x(0) = (ξ, 0, 0, 0)` (machine 1 set up for buffer 4, machine 2 for buffer 3) the
level of buffer 1 is unbounded. -/
theorem example1_case1_all_unbounded (τ : Fin 4 → ℝ) (hτ : ∀ k, 0 < τ k)
    (h3 : 1 < τ 1 + τ 3) (h4 : τ 0 + τ 3 < 1) (h5 : τ 1 + τ 2 < 1)
    (δ : Fin 4 → ℝ) (hδ : ∀ k, 0 < δ k) :
    ∃ ξ₀ : ℝ, ∀ ξ : ℝ, 0 < ξ → ξ₀ ≤ ξ →
      ∀ T : Trajectory (ex1 τ hτ δ (fun k => (hδ k).le)),
        IsClearing (ex1 τ hτ δ (fun k => (hδ k).le)) T → Ex1Initial T ξ →
          ∀ C : ℝ, ∃ t : ℝ, 0 ≤ t ∧ C < T.x (ex1Buf 0) t := by sorry

end KumarSeidman.Reentrant
