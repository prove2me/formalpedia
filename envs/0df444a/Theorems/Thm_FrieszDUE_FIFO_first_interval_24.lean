-- Prove2me | Theorems.Thm_FrieszDUE_FIFO_first_interval_24
-- name    : FrieszDUE.FIFO.first_interval_24
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T07:21:39.043463+00:00
-- url     : https://prove2.me/theorems/147d79be-b11f-4df5-8d28-f2a836511eb5
-- title:
--   (21)–(24), p. 185 — on [0, t₁] with t₁ = β: x(t) = ∫₀ᵗ u, τ(t) = t + α∫₀ᵗ u + β, τ′ = 1 + αu > 0
-- statement:
--   Let $\alpha, \beta > 0$, let the entry rate $u$ be nonnegative and continuous on $[0, \infty)$, and let $\tau$ satisfy the exit-time equation $\tau(t) = t + \alpha x(t) + \beta$ for $t \ge 0$, where $x(t)$ is the mass of the vehicles that entered during $[0,t]$ and are still on the arc at time $t$. Let $t_1 = \tau(0)$ be the exit time of the first vehicle. Then
--
--   1. $t_1 = \beta$ (21);
--   2. for all $t \in [0, t_1]$, $x(t) = \int_0^t u(s)\,ds$ (22);
--   3. for all $t \in [0, t_1]$,
--   $$\tau(t) = t + \alpha \int_0^t u(s)\,ds + \beta \qquad (23);$$
--   4. at every $t \in [0, t_1]$, $\tau$ has derivative $1 + \alpha u(t)$ relative to $[0, t_1]$, and $1 + \alpha u(t) > 0$ (24);
--   5. $\tau$ is strictly increasing on $[0, t_1]$.
--
--   This is the base interval of the partition on which the proof of Theorem 1 proceeds by induction.
--
--   **Formalization Note** Derivatives are taken within the closed interval $[0, t_1]$ (one-sided at the endpoints), matching "for all $t \in [0, t_1]$". The page's conclusion "τ is increasing on $[0,t_1]$" is stated as strict monotonicity, which is what (24) gives and what Theorem 1 asserts.
-- source:
--   Friesz, Bernstein, Smith, Tobin and Wie, A variational inequality formulation of the dynamic network user equilibrium problem, Oper. Res. 41 (1993), p. 185, proof of Theorem 1, (21)–(24)

import Mathlib
import Definitions.Def_FrieszDUE_FIFO_Setting

namespace FrieszDUE.FIFO

theorem first_interval_24 (α β : ℝ) (hα : 0 < α) (hβ : 0 < β) (u : ℝ → ℝ)
    (hu_nonneg : ∀ t, 0 ≤ t → 0 ≤ u t) (hu_cont : ContinuousOn u (Set.Ici 0))
    (τ : ℝ → ℝ) (hτ : IsLinearExitTime α β u τ) :
    tSeq τ 1 = β ∧
      (∀ t ∈ Set.Icc 0 (tSeq τ 1), arcVolume u τ t = ∫ s in (0 : ℝ)..t, u s) ∧
      (∀ t ∈ Set.Icc 0 (tSeq τ 1), τ t = t + α * (∫ s in (0 : ℝ)..t, u s) + β) ∧
      (∀ t ∈ Set.Icc 0 (tSeq τ 1),
        HasDerivWithinAt τ (1 + α * u t) (Set.Icc 0 (tSeq τ 1)) t ∧ 0 < 1 + α * u t) ∧
      StrictMonoOn τ (Set.Icc 0 (tSeq τ 1)) := by sorry

end FrieszDUE.FIFO
