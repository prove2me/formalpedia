-- Prove2me | Theorems.Thm_LittleLaw50_FiniteWindow_theorem_LL1
-- name    : LittleLaw50.FiniteWindow.theorem_LL1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-07T07:52:51.844968+00:00
-- url     : https://prove2.me/theorems/535f0ab6-80a5-4108-92d7-5eee2aea3633
-- title:
--   Theorem LL.1 (Little's Law), p. 537 — L = λW for a sample path observed over [0, T] that is empty at 0 and T
-- statement:
--   Consider one sample path of a queuing system observed over $[0, T]$ with $0 < T < \infty$. Items $i = 1, \dots, M$ arrive at times $a_i$ and leave at times $d_i$, and the system is **empty at $0$ and $T$**: every item arrives and leaves within the window,
--
--   $$0 \le a_i \le d_i \le T \quad \text{for every } i.$$
--
--   Let $n(t)$ be the number of items in the system at time $t$, $A = \int_0^T n(t)\,dt$, $N$ the number of items arriving in $[0, T]$, $L = A/T$ the average number in the system, $\lambda = N/T$ the average arrival rate, and $W = \frac1N \sum_i (d_i - a_i)$ the average wait of an item. Then
--
--   $$L = \lambda W.$$
--
--   The result holds for every sample path: no stationarity, no queue discipline and no service mechanism is assumed. It is the special case of Theorem LL.2 in which no item is present at either end of the window, and the case the paper motivates by a supermarket that is empty at opening and closing time.
--
--   **Formalization Note** The phrase "empty at $0$ and $T$" is read as $0 \le a_i \le d_i \le T$ for every item of the family, the hypothesis of the published cycle identity `KellyStochasticNetworks.littles_law_cycle_identity`; under it $N = M$. Presence is the half-open interval $[a_i, d_i)$, so an item arriving exactly at $0$ is in the system at time $0$; the reading therefore also admits such paths (with $n(0) > 0$), a slightly more permissive hypothesis than $n(0) = 0$ under which the same identity holds. $W$ is the average of the individual waits, not $A/N$. If $N = 0$ the paper's $W$ is undefined; Lean's $W$ is $0$ and both sides equal $0$, so no hypothesis $N \ge 1$ is needed.
-- source:
--   Little, Little's Law as Viewed on Its 50th Anniversary, Oper. Res. 59(3) (2011), DOI 10.1287/opre.1110.0940, p. 537, Theorem LL.1

import Mathlib
import Definitions.Def_KellyStochasticNetworks_Migration
import Definitions.Def_LittleLaw50_FiniteWindow_EmptyWindow

namespace LittleLaw50.FiniteWindow

/-- **Theorem LL.1** (Little 2011, p. 537). A sample path observed over `[0, T]`, `0 < T`, that is
empty at `0` and `T`: every item arrives and leaves within `[0, T]`. Then `L = λ W`, with `L = A/T`
the time average of `n(t)`, `λ = N/T` and `W` the average of the waits `Wᵢ = dᵢ − aᵢ`. -/
theorem theorem_LL1 {M : ℕ} (a d : Fin M → ℝ) (T : ℝ) (hT : 0 < T)
    (hempty : ∀ i, 0 ≤ a i ∧ a i ≤ d i ∧ d i ≤ T) :
    L_LL1 a d T = lam_LL1 a T * W_LL1 a d T := by sorry

end LittleLaw50.FiniteWindow
