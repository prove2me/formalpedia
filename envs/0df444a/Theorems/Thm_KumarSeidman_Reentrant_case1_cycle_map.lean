-- Prove2me | Theorems.Thm_KumarSeidman_Reentrant_case1_cycle_map
-- name    : KumarSeidman.Reentrant.case1_cycle_map
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T12:31:48.911995+00:00
-- url     : https://prove2.me/theorems/2e4904e4-de91-4da2-8b43-66c964be5a71
-- title:
--   Example 1, Case 1, p. 292 — from (ξ, 0, 0, 0) the clearing policy returns to (λξ + β, 0, 0, 0) at T₁ = (λ + τ₂/(1 − τ₂))ξ + α
-- statement:
--   Consider the re-entrant line of Example 1 with processing times $\tau_1, \dots, \tau_4 > 0$ satisfying the critical condition and the capacity conditions
--   $$\tau_2 + \tau_4 > 1, \qquad \tau_1 + \tau_4 < 1, \qquad \tau_2 + \tau_3 < 1, \tag{3–5}$$
--   and with positive set-up times $\delta_1, \delta_2, \delta_3, \delta_4 > 0$. Let $\lambda, \alpha, \beta$ be as in Example 1.
--
--   Then there is $\xi_0$ such that for every $\xi > 0$ with $\xi \ge \xi_0$ the following holds. Along every clearing trajectory started at $x(0) = (\xi, 0, 0, 0)$ with machines 1 and 2 set up for buffers 4 and 3, at the time
--   $$T_1 := \Bigl(\lambda + \frac{\tau_2}{1-\tau_2}\Bigr)\xi + \alpha$$
--   one has
--   $$x(T_1) = (\lambda\xi + \beta,\ 0,\ 0,\ 0),$$
--   and machines 1 and 2 are again set up for buffers 4 and 3.
--
--   This is one full cycle of the clearing policy: the system returns to a state of the same shape with buffer 1 multiplied by $\lambda > 1$ and increased by $\beta$, which drives the instability of Example 1.
--
--   **Formalization Note** The paper states the cycle from an arbitrary start time $T_0$; it is stated here from $T_0 = 0$, the initial state of Case 1 ($t_1 = 0$). "Set up for" at $T_1$ means the run of the machine that started before $T_1$ and has not been replaced before $T_1$: at $T_1$ machine 1 is commencing its set-up for buffer 1. The threshold $\xi_0$ may depend on $\tau$ and $\delta$ ("$\xi > 0$ is large enough").
-- source:
--   Kumar & Seidman, Dynamic Instabilities and Stabilization Methods in Distributed Real-Time Scheduling of Manufacturing Systems, IEEE Trans. Automat. Control 35(3), 1990, p. 292, §III Example 1, Case 1 (t₁₃, λ, α, β and the paragraph 'The important feature to note …')

import Mathlib
import Definitions.Def_KumarSeidman_Reentrant_System
import Definitions.Def_KumarSeidman_Reentrant_Trajectory
import Definitions.Def_KumarSeidman_Reentrant_Clearing
import Definitions.Def_KumarSeidman_Reentrant_Example1

namespace KumarSeidman.Reentrant

/-- **Example 1, Case 1: the cycle map** (§III, p. 292). With `τ₁, …, τ₄ > 0` satisfying
(3)–(5) and set-up times `δ₁, …, δ₄ > 0`, there is `ξ₀` such that for every `ξ > 0` with
`ξ ≥ ξ₀` and every clearing trajectory started at `x(0) = (ξ, 0, 0, 0)` with machines 1 and 2
set up for buffers 4 and 3, at the time `T₁ := (λ + τ₂/(1 - τ₂))ξ + α` one has
`x(T₁) = (λξ + β, 0, 0, 0)` and machines 1 and 2 are again set up for buffers 4 and 3, where
`λ = τ₄/(1 - τ₂)`, `α = (τ₄ + 1)(δ₁ + δ₂)/(1 - τ₂) + δ₃(τ₄ + 1) + δ₄` and
`β = τ₄(δ₁ + δ₂)/(1 - τ₂) + τ₄δ₃ + δ₄`. -/
theorem case1_cycle_map (τ : Fin 4 → ℝ) (hτ : ∀ k, 0 < τ k)
    (h3 : 1 < τ 1 + τ 3) (h4 : τ 0 + τ 3 < 1) (h5 : τ 1 + τ 2 < 1)
    (δ : Fin 4 → ℝ) (hδ : ∀ k, 0 < δ k) :
    ∃ ξ₀ : ℝ, ∀ ξ : ℝ, 0 < ξ → ξ₀ ≤ ξ →
      ∀ T : Trajectory (ex1 τ hτ δ (fun k => (hδ k).le)),
        IsClearing (ex1 τ hτ δ (fun k => (hδ k).le)) T → Ex1Initial T ξ →
          let T₁ := (ex1Lambda τ + τ 1 / (1 - τ 1)) * ξ + ex1Alpha τ δ
          T.x (ex1Buf 0) T₁ = ex1Lambda τ * ξ + ex1Beta τ δ ∧
          T.x (ex1Buf 1) T₁ = 0 ∧ T.x (ex1Buf 2) T₁ = 0 ∧ T.x (ex1Buf 3) T₁ = 0 ∧
          T.IsSetUpFor 0 T₁ (ex1Buf 3) ∧ T.IsSetUpFor 1 T₁ (ex1Buf 2) := by sorry

end KumarSeidman.Reentrant
