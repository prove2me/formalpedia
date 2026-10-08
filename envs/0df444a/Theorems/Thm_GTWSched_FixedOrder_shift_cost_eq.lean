-- Prove2me | Theorems.Thm_GTWSched_FixedOrder_shift_cost_eq
-- name    : GTWSched.FixedOrder.shift_cost_eq
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T07:39:43.108599+00:00
-- url     : https://prove2.me/theorems/9c0ed9b0-f6e2-4b2c-9125-764b9882e178
-- title:
--   §2.2, p. 337 — shifting a balanced block does not change total discrepancy
-- statement:
--   Consider a feasible fixed-order schedule for tasks $0,\ldots,m$, whose final block consists of tasks $j,\ldots,m$. Suppose this block contains equally many tasks that start later than preferred and tasks that start no later than preferred. Let $\delta\ge0$ be no greater than the distance to the first stopping event: the time-zero boundary or the preceding block, and the preferred start of any late task. Shifting the entire final block earlier by $\delta$ preserves total discrepancy:
--
--   $$
--   \operatorname{cost}_{m+1}(\operatorname{shift}_{j:m}(s,\delta))
--   =\operatorname{cost}_{m+1}(s).
--   $$
--
--   This is the cost-preservation claim used when the algorithm shifts a balanced block.
--
--   **Formalization Note** Task $i$ corresponds to the paper's $T_{i+1}$. The explicit bound on $\delta$ records the algorithm's first stopping event.
-- source:
--   Garey, Tarjan & Wilfong, One-Processor Scheduling with Symmetric Earliness and Tardiness Penalties, Math. Oper. Res. 13 (1988), p. 337, §2.2, balanced-block shift

import Mathlib
import Definitions.Def_GTWSched_FixedOrder_Algorithm

namespace GTWSched.FixedOrder

/-- §2.2, p. 337: shifting a balanced final block until the first stopping
event leaves total discrepancy unchanged. -/
theorem shift_cost_eq (a l s : ℕ → ℝ) (m j : ℕ) (δ : ℝ)
    (hfeas : FixedFeasible l (m + 1) s)
    (hblock : IsBlock l (m + 1) s j m)
    (hbalance : decCount a s j m = incCount a s j m)
    (hpositive : s j ≠ 0)
    (hδ : 0 ≤ δ ∧ δ ≤ shiftAmount a l s j m) :
    cost a (m + 1) (shiftRange s j m δ) = cost a (m + 1) s := by sorry

end GTWSched.FixedOrder
