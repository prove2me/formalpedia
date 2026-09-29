-- Prove2me | Theorems.Thm_McNaughtonSched_SingleProc_ratio_order_minimal_zero_deadlines
-- name    : McNaughtonSched.SingleProc.ratio_order_minimal_zero_deadlines
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T15:01:40.565112+00:00
-- url     : https://prove2.me/theorems/94ba4bc3-efd8-4c44-941c-5c2551f98d80
-- title:
--   Theorem 2.3 — with all deadlines 0, unsplit decreasing-$r_i$ order minimizes total loss
-- statement:
--   Consider $m$ tasks on a single processor with processing times $a_i > 0$ and penalties $p_i \ge 0$, and suppose every deadline is at the present, $d_1 = d_2 = \dots = d_m = 0$, so that the loss on $(i)$ is $p_i C_i$. Let $\sigma$ order the tasks by decreasing ratio $r_i = p_i/a_i$, and let $S_\sigma$ be the schedule that processes the tasks without splits and without unused time in that order, task $\sigma(k)$ running from $\sum_{l<k} a_{\sigma(l)}$ to $\sum_{l\le k} a_{\sigma(l)}$. Then $S_\sigma$ is feasible and
--
--   $$
--   c(S_\sigma) \le c(S) \qquad \text{for every feasible schedule } S,
--   $$
--
--   where the competitors $S$ may split tasks and leave the processor idle.
--
--   This is the ratio rule for the total weighted completion time on one machine, in its preemptive form.
--
--   **Formalization Note** The page leaves "with no unused time" implicit here (Theorem 2.4 states it); the sequenced schedule builds it in. Ties among equal ratios may be broken in any order. The deadlines are kept as a parameter with the hypothesis $d_i = 0$, so the statement is visibly the special case of Theorem 2.4. $p_i \ge 0$ is the penalty sign, needed as in Theorem 2.2; $a_i > 0$ is the standing assumption.
-- source:
--   McNaughton, Scheduling with Deadlines and Loss Functions, Management Science 6(1), 1959, p. 5, Theorem 2.3

import Mathlib
import Definitions.Def_McNaughtonSched_SingleProc_Model

namespace McNaughtonSched.SingleProc

theorem ratio_order_minimal_zero_deadlines {m : ℕ} (a p d : Fin m → ℝ)
    (ha : ∀ i, 0 < a i) (hp : ∀ i, 0 ≤ p i) (hd : ∀ i, d i = 0)
    (σ : Equiv.Perm (Fin m)) (hσ : InRatioOrder a p σ) :
    IsFeasible a (seqSchedule a σ) ∧
      ∀ S : Schedule m, IsFeasible a S →
        totalLoss p d (seqSchedule a σ) ≤ totalLoss p d S := by sorry

end McNaughtonSched.SingleProc
