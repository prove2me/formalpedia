-- Prove2me | Theorems.Thm_KumarSeidman_Reentrant_example1_clearing_unstable
-- name    : KumarSeidman.Reentrant.example1_clearing_unstable
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T12:35:26.372989+00:00
-- url     : https://prove2.me/theorems/b5601d92-3f95-4571-aa86-95046f2fadb2
-- title:
--   Example 1, pp. 291–292 — on the re-entrant line with τ₂ + τ₄ > 1, the clearing policy is unstable, with or without set-up times
-- statement:
--   Consider the manufacturing system of Example 1: one part type arriving at rate $1$ visits machine 1, machine 2, machine 2 and machine 1, through buffers $1, 2, 3, 4$, with processing times $\tau_1, \dots, \tau_4 > 0$ satisfying the critical condition (3) and the capacity condition (1), i.e.
--   $$\tau_2 + \tau_4 > 1, \tag{3}$$
--   $$\tau_1 + \tau_4 < 1, \tag{4}$$
--   $$\tau_2 + \tau_3 < 1. \tag{5}$$
--   Start from $x(0) = (\xi, 0, 0, 0)$ with machine 1 set up for buffer 4 and machine 2 set up for buffer 3, and schedule with a clearing policy.
--
--   1. **Case 1 (positive set-up times).** If $\delta_1, \delta_2, \delta_3, \delta_4 > 0$, there is $\xi_0$ such that for every $\xi > 0$ with $\xi \ge \xi_0$, a clearing trajectory from this initial state exists, and along every such trajectory
--   $$\sup_{0 \le t < \infty} x_1(t) = +\infty.$$
--   2. **Case 2 (no set-up times).** If $\delta_1 = \delta_2 = \delta_3 = \delta_4 = 0$, then for every $\xi > 0$ a clearing trajectory from this initial state exists, and along every such trajectory $\sup_{0 \le t < \infty} x_1(t) = +\infty$.
--
--   So the system is unstable under clearing even though every machine has spare capacity; in Case 2 the instability is caused purely by starvation of machines by upstream machines, not by set-up times.
--
--   **Formalization Note** The paper's conclusions are $\lim_{n\to\infty} x_1(T_n) = +\infty$ (Case 1) and $\lim_{n\to\infty} x_1(t_{4n+1}) = +\infty$ (Case 2); their common content, unboundedness of $x_1$ on $[0,\infty)$, is stated as: for every $C$ there is $t \ge 0$ with $x_1(t) > C$. The existence of a clearing trajectory is part of the statement, so the universal half is not vacuous. "Clearing" uses the reading of Definition 1 recorded with the clearing definition (a target buffer counts as nonempty when it is demanding). Time is real, and the model has no transport delays.
-- source:
--   Kumar & Seidman, Dynamic Instabilities and Stabilization Methods in Distributed Real-Time Scheduling of Manufacturing Systems, IEEE Trans. Automat. Control 35(3), 1990, pp. 291–292, §III Example 1, Cases 1 and 2

import Mathlib
import Definitions.Def_KumarSeidman_Reentrant_System
import Definitions.Def_KumarSeidman_Reentrant_Trajectory
import Definitions.Def_KumarSeidman_Reentrant_Clearing
import Definitions.Def_KumarSeidman_Reentrant_Example1

namespace KumarSeidman.Reentrant

/-- **Example 1** (Kumar–Seidman 1990, §III, pp. 291–292). Consider the re-entrant line of
Example 1 with processing times `τ₁, …, τ₄ > 0` (Lean `τ 0, …, τ 3`) satisfying the critical
condition (3) `τ₂ + τ₄ > 1` and the capacity condition (1), i.e. (4) `τ₁ + τ₄ < 1` and
(5) `τ₂ + τ₃ < 1`. Start from `x(0) = (ξ, 0, 0, 0)` with machine 1 set up for buffer 4 and
machine 2 set up for buffer 3.

* (Case 1, positive set-up times) If `δ₁, …, δ₄ > 0`, there is `ξ₀` such that for every
  `ξ > 0` with `ξ ≥ ξ₀` a clearing trajectory from that initial state exists, and along every
  such trajectory the level `x₁` of buffer 1 is unbounded on `[0, ∞)`.
* (Case 2, no set-up times) If `δ₁ = ⋯ = δ₄ = 0`, the same holds for every `ξ > 0`. -/
theorem example1_clearing_unstable (τ : Fin 4 → ℝ) (hτ : ∀ k, 0 < τ k)
    (h3 : 1 < τ 1 + τ 3) (h4 : τ 0 + τ 3 < 1) (h5 : τ 1 + τ 2 < 1) :
    (∀ (δ : Fin 4 → ℝ) (hδ : ∀ k, 0 < δ k),
      ∃ ξ₀ : ℝ, ∀ ξ : ℝ, 0 < ξ → ξ₀ ≤ ξ →
        (∃ T : Trajectory (ex1 τ hτ δ (fun k => (hδ k).le)),
          IsClearing (ex1 τ hτ δ (fun k => (hδ k).le)) T ∧ Ex1Initial T ξ) ∧
        ∀ T : Trajectory (ex1 τ hτ δ (fun k => (hδ k).le)),
          IsClearing (ex1 τ hτ δ (fun k => (hδ k).le)) T → Ex1Initial T ξ →
            ∀ C : ℝ, ∃ t : ℝ, 0 ≤ t ∧ C < T.x (ex1Buf 0) t) ∧
    (∀ ξ : ℝ, 0 < ξ →
      (∃ T : Trajectory (ex1 τ hτ (fun _ => 0) (fun _ => le_refl 0)),
          IsClearing (ex1 τ hτ (fun _ => 0) (fun _ => le_refl 0)) T ∧ Ex1Initial T ξ) ∧
        ∀ T : Trajectory (ex1 τ hτ (fun _ => 0) (fun _ => le_refl 0)),
          IsClearing (ex1 τ hτ (fun _ => 0) (fun _ => le_refl 0)) T → Ex1Initial T ξ →
            ∀ C : ℝ, ∃ t : ℝ, 0 ≤ t ∧ C < T.x (ex1Buf 0) t) := by sorry

end KumarSeidman.Reentrant
