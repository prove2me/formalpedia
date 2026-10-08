-- Prove2me | Theorems.Thm_FrieszDUE_FIFO_theorem_1
-- name    : FrieszDUE.FIFO.theorem_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T07:21:56.253097+00:00
-- url     : https://prove2.me/theorems/e59665a2-4314-445d-a3fc-611802bf5e48
-- title:
--   Theorem 1, p. 185 — under linear arc delay αx(t) + β the arc exit time τ is strictly increasing, so τ⁻¹ exists (FIFO)
-- statement:
--   Consider a single arc of a traffic network on which vehicles enter at a nonnegative, continuous **entry rate** $u(t)$, $t \ge 0$, the first vehicle entering at time $0$. The arc has the **linear delay function** (18)
--   $$D(t) = \alpha\, x(t) + \beta, \qquad \alpha, \beta > 0,$$
--   where $x(t)$ is the arc volume at time $t$: the inflow mass of the vehicles that entered during $[0,t]$ and have not exited by time $t$. A vehicle entering at time $t$ exits at $\tau(t) = t + D(t)$.
--
--   **Theorem 1.** Every exit-time function $\tau$ satisfying
--   $$\tau(t) = t + \alpha\, x(t) + \beta \quad \text{for all } t \ge 0$$
--   is strictly increasing on $[0, \infty)$; hence it is injective there and the inverse function $\tau^{-1}$ exists.
--
--   Strict monotonicity of the exit time is the first-in-first-out (FIFO) property: a vehicle that enters the arc later cannot exit earlier, so no overtaking occurs. It is what makes the path exit-time functions invertible, which the dynamic user-equilibrium model of the paper requires.
--
--   **Formalization Note** The nonnegativity and continuity of $u$ on $[0, \infty)$ are added hypotheses: the theorem names none, nonnegativity is implicit in "entry rate", and the remark after the proof extends the result to "all continuous entry rate patterns". The exit time is pinned only by the implicit equation; no monotonicity or invertibility of $\tau$ is assumed, and the volume is not written with $\tau^{-1}$. Monotonicity is claimed only on $[0, \infty)$, the entry times the equation constrains.
-- source:
--   Friesz, Bernstein, Smith, Tobin and Wie, A variational inequality formulation of the dynamic network user equilibrium problem, Oper. Res. 41 (1993), p. 185, Theorem 1, with (18) and the remark on p. 186

import Mathlib
import Definitions.Def_FrieszDUE_FIFO_Setting

namespace FrieszDUE.FIFO

theorem theorem_1 (α β : ℝ) (hα : 0 < α) (hβ : 0 < β) (u : ℝ → ℝ)
    (hu_nonneg : ∀ t, 0 ≤ t → 0 ≤ u t) (hu_cont : ContinuousOn u (Set.Ici 0))
    (τ : ℝ → ℝ) (hτ : IsLinearExitTime α β u τ) :
    StrictMonoOn τ (Set.Ici 0) ∧ Set.InjOn τ (Set.Ici 0) := by sorry

end FrieszDUE.FIFO
