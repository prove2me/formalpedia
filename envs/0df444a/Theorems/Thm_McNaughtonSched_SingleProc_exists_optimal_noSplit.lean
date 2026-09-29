-- Prove2me | Theorems.Thm_McNaughtonSched_SingleProc_exists_optimal_noSplit
-- name    : McNaughtonSched.SingleProc.exists_optimal_noSplit
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T15:01:06.026324+00:00
-- url     : https://prove2.me/theorems/17a0e4aa-7324-45c1-924f-ca895366f44f
-- title:
--   Theorem 2.2 — on one processor some optimal schedule splits no task
-- statement:
--   Consider $m$ tasks on a single processor with processing times $a_i > 0$, penalties $p_i \ge 0$ and arbitrary deadlines $d_i$, and let $c(S)$ be the total loss of a schedule $S$ (the sum over tasks of $p_i\max(0, C_i(S) - d_i)$, where $C_i(S)$ is the completion time of $(i)$). Then there is a feasible schedule $S_0$ in which no task is split and which is optimal among **all** feasible schedules, split or not, with or without idle time:
--
--   $$
--   \exists\, S_0 \text{ feasible, unsplit}:\quad c(S_0) \le c(S) \quad \text{for every feasible } S .
--   $$
--
--   Splitting a task therefore never helps on a single processor; the search for an optimum can be restricted to the finitely many orders of unsplit tasks.
--
--   **Formalization Note** "Optimal solution" is stated as the existence of a minimizer over every feasible schedule. "No task is split" means each task has exactly one piece. The hypothesis $p_i \ge 0$ (the $p_i$ are penalties) is needed: with a negative penalty and idle time allowed, the loss is unbounded below and no optimum exists. $a_i > 0$ is the standing assumption that tasks take time.
-- source:
--   McNaughton, Scheduling with Deadlines and Loss Functions, Management Science 6(1), 1959, p. 4, Theorem 2.2

import Mathlib
import Definitions.Def_McNaughtonSched_SingleProc_Model

namespace McNaughtonSched.SingleProc

theorem exists_optimal_noSplit {m : ℕ} (a p d : Fin m → ℝ)
    (ha : ∀ i, 0 < a i) (hp : ∀ i, 0 ≤ p i) :
    ∃ S₀ : Schedule m, IsFeasible a S₀ ∧ NoSplit S₀ ∧
      ∀ S : Schedule m, IsFeasible a S → totalLoss p d S₀ ≤ totalLoss p d S := by sorry

end McNaughtonSched.SingleProc
