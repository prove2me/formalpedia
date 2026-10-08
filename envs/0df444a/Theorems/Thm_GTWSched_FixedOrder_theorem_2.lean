-- Prove2me | Theorems.Thm_GTWSched_FixedOrder_theorem_2
-- name    : GTWSched.FixedOrder.theorem_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T07:40:52.34219+00:00
-- url     : https://prove2.me/theorems/257c7f5d-df0c-43cb-a4d4-09737c3538da
-- title:
--   THEOREM 2, p. 338 — the block-shifting algorithm minimizes total discrepancy in a fixed order
-- statement:
--   Let tasks have nonnegative preferred starting times $a_i$ and nonnegative lengths $l_i$. For any $n\ge0$, the block-shifting algorithm of §2.2 produces a feasible schedule $S_n$ for the first $n$ tasks in their prescribed order, and its total discrepancy is no greater than that of every other feasible schedule $S$ in the same order:
--
--   $$
--   \operatorname{cost}_n(S_n)\le\operatorname{cost}_n(S).
--   $$
--
--   Feasibility and optimality together characterize the algorithm's output, including the empty schedule.
--
--   **Formalization Note** Task $i$ corresponds to $T_{i+1}$. Every start is nonnegative; idle time is allowed, and the comparison class contains all schedules respecting the fixed order.
-- source:
--   Garey, Tarjan & Wilfong, One-Processor Scheduling with Symmetric Earliness and Tardiness Penalties, Math. Oper. Res. 13 (1988), p. 338, THEOREM 2

import Mathlib
import Definitions.Def_GTWSched_FixedOrder_Algorithm

namespace GTWSched.FixedOrder

/-- THEOREM 2, p. 338: the algorithm returns a feasible minimum-cost
schedule among all schedules of the first n tasks in the prescribed order. -/
theorem theorem_2 (a l : ℕ → ℝ) (ha : ∀ i, 0 ≤ a i) (hl : ∀ i, 0 ≤ l i)
    (n : ℕ) :
    FixedFeasible l n (sched a l n) ∧
      ∀ s : ℕ → ℝ, FixedFeasible l n s →
        cost a n (sched a l n) ≤ cost a n s := by sorry

end GTWSched.FixedOrder
