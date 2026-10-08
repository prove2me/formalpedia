-- Prove2me | Theorems.Thm_GTWSched_FixedOrder_case_2_2_block
-- name    : GTWSched.FixedOrder.case_2_2_block
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T07:40:24.986437+00:00
-- url     : https://prove2.me/theorems/bb0b0e97-0994-4b7d-9888-76c4fa5f6689
-- title:
--   THEOREM 2 proof, Case 2.2, p. 338 — an earlier new task cannot lower the last block's discrepancy
-- statement:
--   In Case 2, let $R$ append the new task to $S_n$ at the preceding task's completion time, and let $[j,n]$ be the final block of $R$. For any feasible fixed-order schedule $S$ with the new task starting earlier than in $R$, every task of this final block starts no later in $S$ than in $R$, and its total block discrepancy cannot be smaller:
--
--   $$
--   s_i\le r_i\quad(j\le i\le n),\qquad
--   \sum_{i=j}^{n}|r_i-a_i|\le\sum_{i=j}^{n}|s_i-a_i|.
--   $$
--
--   The claim is applied to the actual block formed by the algorithm; the count condition on an arbitrary block would not suffice.
--
--   **Formalization Note** Task $i$ is the paper's $T_{i+1}$. Feasibility includes nonnegative starts and the prescribed task order.
-- source:
--   Garey, Tarjan & Wilfong, One-Processor Scheduling with Symmetric Earliness and Tardiness Penalties, Math. Oper. Res. 13 (1988), p. 338, THEOREM 2 proof, Case 2.2

import Mathlib
import Definitions.Def_GTWSched_FixedOrder_Algorithm

namespace GTWSched.FixedOrder

/-- Case 2.2 of THEOREM 2, p. 338: an alternative that places the new task
earlier moves every task of R's final block earlier and cannot lower that
block's total discrepancy. -/
theorem case_2_2_block (a l : ℕ → ℝ) (ha : ∀ i, 0 ≤ a i)
    (hl : ∀ i, 0 ≤ l i) (n : ℕ) (hn : 0 < n)
    (hlate : a n < sched a l n (n - 1) + l (n - 1))
    (s : ℕ → ℝ) (hs : FixedFeasible l (n + 1) s) :
    let r := place (sched a l n) n (sched a l n (n - 1) + l (n - 1))
    let j := blockStart l r n
    s n < r n →
      (∀ i, j ≤ i → i ≤ n → s i ≤ r i) ∧
      (∑ i ∈ Finset.Icc j n, |r i - a i|) ≤
        ∑ i ∈ Finset.Icc j n, |s i - a i| := by sorry

end GTWSched.FixedOrder
