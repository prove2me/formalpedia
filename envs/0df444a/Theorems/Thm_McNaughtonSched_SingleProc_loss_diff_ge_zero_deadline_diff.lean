-- Prove2me | Theorems.Thm_McNaughtonSched_SingleProc_loss_diff_ge_zero_deadline_diff
-- name    : McNaughtonSched.SingleProc.loss_diff_ge_zero_deadline_diff
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T15:02:02.376581+00:00
-- url     : https://prove2.me/theorems/e93ce2dd-cd33-4ec0-b9ed-c27f95041ecf
-- title:
--   Proof of Theorem 2.4 — $c(S') - c(S) \ge c^*(S') - c^*(S)$ when no task of $S$ finishes early
-- statement:
--   Consider $m$ tasks on a single processor with processing times $a_i > 0$, penalties $p_i \ge 0$ and deadlines $d_i$. For a schedule $T$ let $c(T)$ be its total loss, and let $c^*(T)$ be the total loss of $T$ computed on the assumption that $d_1 = d_2 = \dots = d_m = 0$. Let $S$ be the schedule that processes the tasks without splits and without unused time in some order $\sigma$, and suppose no task finishes before its deadline in $S$: $d_i \le C_i(S)$ for every $i$. Then for every feasible schedule $S'$,
--
--   $$
--   c(S') - c(S) \;\ge\; c^*(S') - c^*(S).
--   $$
--
--   This is the comparison in the proof of Theorem 2.4 that transfers the zero-deadline optimality of Theorem 2.3 to arbitrary deadlines.
--
--   **Formalization Note** The order $\sigma$ is arbitrary here: the display needs only that no task of $S$ is early, not the ratio order. $c^*$ is the total loss with the zero deadline vector. $p_i \ge 0$ and $a_i > 0$ are the standing assumptions; $S'$ ranges over all feasible schedules, not only unsplit ones.
-- source:
--   McNaughton, Scheduling with Deadlines and Loss Functions, Management Science 6(1), 1959, p. 6, first display (proof of Theorem 2.4); c* defined on p. 5

import Mathlib
import Definitions.Def_McNaughtonSched_SingleProc_Model

namespace McNaughtonSched.SingleProc

theorem loss_diff_ge_zero_deadline_diff {m : ℕ} (a p d : Fin m → ℝ)
    (ha : ∀ i, 0 < a i) (hp : ∀ i, 0 ≤ p i)
    (σ : Equiv.Perm (Fin m)) (hlate : ∀ i, d i ≤ completion (seqSchedule a σ) i)
    (S' : Schedule m) (hS' : IsFeasible a S') :
    totalLoss p 0 S' - totalLoss p 0 (seqSchedule a σ) ≤
      totalLoss p d S' - totalLoss p d (seqSchedule a σ) := by sorry

end McNaughtonSched.SingleProc
