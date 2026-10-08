-- Prove2me | Theorems.Thm_LittleLaw50_FiniteWindow_theorem_LL2
-- name    : LittleLaw50.FiniteWindow.theorem_LL2
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-07T07:52:59.796784+00:00
-- url     : https://prove2.me/theorems/2d598f1a-2962-4880-8176-0d3be226d692
-- title:
--   Theorem LL.2 (Little's Law over [0, T]), p. 539 — L = λW for every sample path observed over [0, T], 0 < T < ∞
-- statement:
--   Consider one sample path of a queuing system observed over a finite window $[0, T]$ with $0 < T < \infty$. Items $i = 1, \dots, M$ arrive at times $a_i$ and leave at times $d_i \ge a_i$. Items may already be in the system at time $0$ and may still be there at time $T$ (such an item is given any departure time $d_i > T$). Let
--
--   1. $n(t)$ be the number of items in the system at time $t$, and $A = \int_0^T n(t)\,dt$;
--   2. $S(T)$ be the cumulative number of items in the system over $[0, T]$: the items present at $t = 0$ plus the items arriving in $[0, T]$;
--   3. $w_i(T) = \max(0, \min(d_i, T) - \max(a_i, 0))$ be the time item $i$ spends in the system during $[0, T]$;
--   4. $L(T) = A/T$, $\lambda(T) = S(T)/T$, and $W(T)$ the average of $w_i(T)$ over the $S(T)$ counted items.
--
--   Then
--
--   $$L(T) = \lambda(T)\, W(T).$$
--
--   This is Little's Law over a finite window with permissible initial and final queues. It holds exactly for every sample path, whether or not the system is ever empty (§2.2.3, Corollary (1)) and whether or not there is any service operation (Corollary (2)); no stationarity, queue discipline or limit is involved. Theorem LL.1 is its special case for a window empty at both ends.
--
--   **Formalization Note** Presence is half-open, $[a_i, d_i)$; an item arriving exactly at $0$ is counted in $S(T)$ once, as an arrival in $[0, T]$. The family may contain items never present during $[0, T]$; they are not counted and contribute nothing. $W(T)$ is the average of the truncated times in window, never defined as $A/S(T)$; that equality is the content of the theorem. The hypothesis $a_i \le d_i$ (an item leaves no earlier than it arrives) is the paper's $W_i \ge 0$. If $S(T) = 0$, then $A = 0$, the paper's $W(T)$ is undefined, Lean's value is $0$, and both sides are $0$.
-- source:
--   Little, Little's Law as Viewed on Its 50th Anniversary, Oper. Res. 59(3) (2011), DOI 10.1287/opre.1110.0940, p. 539, Theorem LL.2

import Mathlib
import Definitions.Def_KellyStochasticNetworks_Migration
import Definitions.Def_LittleLaw50_FiniteWindow_Window

namespace LittleLaw50.FiniteWindow

/-- **Theorem LL.2** (Little's Law over `[0, T]`; Little 2011, p. 539). For any sample path
observed over `[0, T]` with `0 < T`, possibly with items present at `0` and at `T`,
`L(T) = λ(T) W(T)`, with `L(T) = A/T`, `λ(T) = S(T)/T` and `W(T)` the average over the `S(T)`
counted items of their time in the system during `[0, T]`. -/
theorem theorem_LL2 {M : ℕ} (a d : Fin M → ℝ) (T : ℝ) (hT : 0 < T)
    (had : ∀ i, a i ≤ d i) :
    Lw Finset.univ a d T = lamw Finset.univ a d T * Ww Finset.univ a d T := by sorry

end LittleLaw50.FiniteWindow
