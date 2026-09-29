-- Prove2me | Theorems.Thm_McNaughtonSched_SingleProc_ratio_order_minimal_of_no_early
-- name    : McNaughtonSched.SingleProc.ratio_order_minimal_of_no_early
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T15:02:33.300619+00:00
-- url     : https://prove2.me/theorems/069c87bb-dfdf-428b-8cea-ec4649f52f1e
-- title:
--   Theorem 2.4 — unsplit decreasing-$r_i$ order without idle time, no task early, is minimal
-- statement:
--   Consider $m$ tasks on a single processor. Task $(i)$ needs $a_i > 0$ units of time, has deadline $d_i$ and penalty rate $p_i \ge 0$: completed at time $C_i$, it incurs the loss $p_i\max(0, C_i - d_i)$. Let $\sigma$ order the tasks by decreasing ratio $r_i = p_i/a_i$, and let $S$ be the schedule that runs the tasks without splitting and without unused time in that order, task $\sigma(k)$ occupying $\bigl[\sum_{l<k} a_{\sigma(l)}, \sum_{l\le k} a_{\sigma(l)}\bigr]$. Suppose that in $S$ no task finishes before its deadline, i.e. $d_i \le C_i(S)$ for all $i$. Then $S$ is a feasible schedule and it is minimal:
--
--   $$
--   c(S) \le c(S') \qquad \text{for every feasible schedule } S',
--   $$
--
--   where $c$ denotes total loss and the competitors $S'$ may split tasks and leave the processor idle.
--
--   The condition is sufficient but not necessary for minimality. It generalizes Theorem 2.3 (all deadlines $0$) and underlies the scheduling procedure the paper proposes for general deadlines.
--
--   **Formalization Note** "Decreasing" is non-increasing, with ties in any order. "Minimal" is stated against every feasible schedule; the conclusion also asserts that the sequenced schedule is feasible. $p_i \ge 0$ (the $p_i$ are penalties) and $a_i > 0$ (tasks take time) are the model's standing assumptions; no sign condition on the deadlines is imposed.
-- source:
--   McNaughton, Scheduling with Deadlines and Loss Functions, Management Science 6(1), 1959, p. 5, Theorem 2.4

import Mathlib
import Definitions.Def_McNaughtonSched_SingleProc_Model

namespace McNaughtonSched.SingleProc

theorem ratio_order_minimal_of_no_early {m : ℕ} (a p d : Fin m → ℝ)
    (ha : ∀ i, 0 < a i) (hp : ∀ i, 0 ≤ p i)
    (σ : Equiv.Perm (Fin m)) (hσ : InRatioOrder a p σ)
    (hlate : ∀ i, d i ≤ completion (seqSchedule a σ) i) :
    IsFeasible a (seqSchedule a σ) ∧
      ∀ S : Schedule m, IsFeasible a S →
        totalLoss p d (seqSchedule a σ) ≤ totalLoss p d S := by sorry

end McNaughtonSched.SingleProc
