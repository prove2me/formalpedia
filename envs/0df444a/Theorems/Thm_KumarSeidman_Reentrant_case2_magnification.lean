-- Prove2me | Theorems.Thm_KumarSeidman_Reentrant_case2_magnification
-- name    : KumarSeidman.Reentrant.case2_magnification
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T12:35:18.187072+00:00
-- url     : https://prove2.me/theorems/ef1b297a-1140-49ca-9e80-060536ab88ef
-- title:
--   Example 1, Case 2, p. 292 — with zero set-up times, x(t₅) = (λξ, 0, 0, 0): a magnified copy of the initial state
-- statement:
--   Consider the re-entrant line of Example 1 with processing times $\tau_1, \dots, \tau_4 > 0$ satisfying
--   $$\tau_2 + \tau_4 > 1, \qquad \tau_1 + \tau_4 < 1, \qquad \tau_2 + \tau_3 < 1, \tag{3–5}$$
--   and with all set-up times zero, $\delta_1 = \delta_2 = \delta_3 = \delta_4 = 0$. Let $\xi > 0$, and let $\lambda = \tau_4/(1-\tau_2)$.
--
--   Along every clearing trajectory started at $x(0) = (\xi, 0, 0, 0)$ with machines 1 and 2 set up for buffers 4 and 3, at the time
--   $$t_5 = \frac{(\tau_2 + \tau_4)\,\xi}{1 - \tau_2}$$
--   one has
--   $$x(t_5) = (\lambda\xi,\ 0,\ 0,\ 0),$$
--   and machines 1 and 2 are again set up for buffers 4 and 3.
--
--   Since $\lambda > 1$, the state at $t_5$ is a magnified version of the initial state; this is the mechanism of the purely starvation-induced instability of Example 1, Case 2.
--
--   **Formalization Note** The paper defines $t_5$ through its stages: $t_2 = t_1 + \xi/(\tau_1^{-1} - 1)$, $t_3 = t_2 + x_2(t_2)/(\tau_2^{-1} - 1)$, $t_4 = t_3 + \tau_3 x_3(t_3)$, $t_5 = t_4 + \tau_4 x_4(t_4)$, with $t_1 = 0$. The closed form $t_5 = (\tau_2+\tau_4)\xi/(1-\tau_2)$ is computed from those stage definitions and is not printed in the paper; it equals Case 1's $T_1$ with every $\delta_k = 0$. The set-up conditions at $t_5$ are the paper's "the state of the system is a magnified version of that at time $t_1$".
-- source:
--   Kumar & Seidman, Dynamic Instabilities and Stabilization Methods in Distributed Real-Time Scheduling of Manufacturing Systems, IEEE Trans. Automat. Control 35(3), 1990, p. 292, §III Example 1, Case 2, Stages 1–4 and 'A computation shows that x₁(t₅) = λξ …'

import Mathlib
import Definitions.Def_KumarSeidman_Reentrant_System
import Definitions.Def_KumarSeidman_Reentrant_Trajectory
import Definitions.Def_KumarSeidman_Reentrant_Clearing
import Definitions.Def_KumarSeidman_Reentrant_Example1

namespace KumarSeidman.Reentrant

/-- **Example 1, Case 2: magnification** (§III, p. 292). With `τ₁, …, τ₄ > 0` satisfying
(3)–(5) and all set-up times zero, for every `ξ > 0` and every clearing trajectory started at
`x(0) = (ξ, 0, 0, 0)` with machines 1 and 2 set up for buffers 4 and 3, at the time
`t₅ = (τ₂ + τ₄)ξ/(1 - τ₂)` one has `x(t₅) = (λξ, 0, 0, 0)` with `λ = τ₄/(1 - τ₂)`, and machines
1 and 2 are again set up for buffers 4 and 3. -/
theorem case2_magnification (τ : Fin 4 → ℝ) (hτ : ∀ k, 0 < τ k)
    (h3 : 1 < τ 1 + τ 3) (h4 : τ 0 + τ 3 < 1) (h5 : τ 1 + τ 2 < 1) (ξ : ℝ) (hξ : 0 < ξ)
    (T : Trajectory (ex1 τ hτ (fun _ => 0) (fun _ => le_refl 0)))
    (hT : IsClearing (ex1 τ hτ (fun _ => 0) (fun _ => le_refl 0)) T) (h0 : Ex1Initial T ξ) :
    let t₅ := (τ 1 + τ 3) * ξ / (1 - τ 1)
    T.x (ex1Buf 0) t₅ = ex1Lambda τ * ξ ∧
    T.x (ex1Buf 1) t₅ = 0 ∧ T.x (ex1Buf 2) t₅ = 0 ∧ T.x (ex1Buf 3) t₅ = 0 ∧
    T.IsSetUpFor 0 t₅ (ex1Buf 3) ∧ T.IsSetUpFor 1 t₅ (ex1Buf 2) := by sorry

end KumarSeidman.Reentrant
