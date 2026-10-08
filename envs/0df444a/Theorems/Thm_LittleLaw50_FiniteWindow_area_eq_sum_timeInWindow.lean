-- Prove2me | Theorems.Thm_LittleLaw50_FiniteWindow_area_eq_sum_timeInWindow
-- name    : LittleLaw50.FiniteWindow.area_eq_sum_timeInWindow
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-07T07:52:56.138952+00:00
-- url     : https://prove2.me/theorems/3f6b040a-f8a3-48ed-b791-fb6e73e67638
-- title:
--   Proof of Theorem LL.2, p. 539 — the area A under n(t) over [0, T] is the total time in system during [0, T] of the S(T) items, so W = A/S(T)
-- statement:
--   Consider one sample path observed over $[0, T]$ with $T > 0$: items $i = 1, \dots, M$ arrive at $a_i$ and leave at $d_i \ge a_i$, items may be present at time $0$ and at time $T$, and $n(t)$ is the number of items in the system at time $t$. Let $S(T)$ be the number of items in the system over $[0, T]$ (those present at $0$ plus those arriving in $[0, T]$), let $w_i(T) = \max(0, \min(d_i, T) - \max(a_i, 0))$ be the time item $i$ spends in the system during $[0, T]$, and let $W(T)$ be the average of the $w_i(T)$ over the $S(T)$ counted items. Then
--
--   $$A = \int_0^T n(t)\,dt = \sum_{i \text{ counted in } S(T)} w_i(T), \qquad\text{and hence}\qquad W(T) = \frac{A}{S(T)}.$$
--
--   This is the step "$W = A/S(T)$" of the paper's proof of Theorem LL.2: the area under $n(t)$ is used once to compute $L$ and once to compute $W$, because an item in the system during $[0, T]$ accumulates time in system exactly while it is counted by $n(t)$. Truncation at the window's edges is what makes the identity exact even with nonzero starting and ending queues.
--
--   **Formalization Note** Presence is half-open, $[a_i, d_i)$. Items that leave by time $0$ or arrive after $T$ are in the family but are not counted in $S(T)$ and contribute $w_i(T) = 0$. When $S(T) = 0$, both $A$ and Lean's value of $W(T)$ are $0$.
-- source:
--   Little, Little's Law as Viewed on Its 50th Anniversary, Oper. Res. 59(3) (2011), DOI 10.1287/opre.1110.0940, p. 539, proof of Theorem LL.2, display W = A/S(T)

import Mathlib
import Definitions.Def_KellyStochasticNetworks_Migration
import Definitions.Def_LittleLaw50_FiniteWindow_Window

namespace LittleLaw50.FiniteWindow

/-- **Proof of Theorem LL.2** (Little 2011, p. 539), display `W = A/S(T)`. The area
`A = ∫₀ᵀ n(t) dt` equals the total time that the `S(T)` counted items spend in the system during
`[0, T]`, and hence `W(T) = A / S(T)`. -/
theorem area_eq_sum_timeInWindow {M : ℕ} (a d : Fin M → ℝ) (T : ℝ) (hT : 0 < T)
    (had : ∀ i, a i ≤ d i) :
    area Finset.univ a d T
        = ∑ i ∈ countedItems Finset.univ a d T, timeInWindow a d T i ∧
      Ww Finset.univ a d T = area Finset.univ a d T / cumCount Finset.univ a d T := by sorry

end LittleLaw50.FiniteWindow
