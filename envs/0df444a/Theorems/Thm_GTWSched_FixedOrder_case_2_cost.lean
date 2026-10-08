-- Prove2me | Theorems.Thm_GTWSched_FixedOrder_case_2_cost
-- name    : GTWSched.FixedOrder.case_2_cost
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T07:39:58.036348+00:00
-- url     : https://prove2.me/theorems/93453e9f-714a-42ac-a733-205896f5ee25
-- title:
--   THEOREM 2 proof, Case 2, p. 338 — cost of appending a late task
-- statement:
--   Let $S_n$ be the algorithm's schedule for $n\ge1$ tasks. If the preceding task finishes after task $n$'s preferred starting time, then the algorithm appends task $n$ at that finish time and possibly shifts the final block. The resulting total cost is
--
--   $$
--   \operatorname{cost}_{n+1}(S_{n+1})
--   =\operatorname{cost}_n(S_n)+s_{n-1}+l_{n-1}-a_n.
--   $$
--
--   This identity isolates the new task's discrepancy in Case 2 of the optimality proof.
--
--   **Formalization Note** The paper's task $T_{n+1}$ is task $n$ here. Preferred starts and lengths are nonnegative, as in the paper's model.
-- source:
--   Garey, Tarjan & Wilfong, One-Processor Scheduling with Symmetric Earliness and Tardiness Penalties, Math. Oper. Res. 13 (1988), p. 338, THEOREM 2 proof, Case 2

import Mathlib
import Definitions.Def_GTWSched_FixedOrder_Algorithm

namespace GTWSched.FixedOrder

/-- Case 2 of THEOREM 2, p. 338: inserting the late new task adds precisely
its discrepancy; a subsequent balanced-block shift costs nothing. -/
theorem case_2_cost (a l : ℕ → ℝ) (ha : ∀ i, 0 ≤ a i) (hl : ∀ i, 0 ≤ l i)
    (n : ℕ) (hn : 0 < n)
    (hlate : a n < sched a l n (n - 1) + l (n - 1)) :
    cost a (n + 1) (sched a l (n + 1)) =
      cost a n (sched a l n) +
        (sched a l n (n - 1) + l (n - 1) - a n) := by sorry

end GTWSched.FixedOrder
