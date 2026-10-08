-- Prove2me | Theorems.Thm_IgnallSchrage_MeanCompletion_example_p408
-- name    : IgnallSchrage.MeanCompletion.example_p408
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T17:31:34.098603+00:00
-- url     : https://prove2.me/theorems/bc06b3c9-64fc-46fa-afce-3f80cc6e3a07
-- title:
--   p. 408 — the 3-job example: 1–2 is optimal for jobs 1, 2, but 3–2–1 is the optimum for all three
-- statement:
--   Take three jobs with processing times
--
--   | job | 1 | 2 | 3 |
--   |---|---|---|---|
--   | $a_i$ | 2 | 10 | 1 |
--   | $b_i$ | 11 | 3 | 8 |
--
--   1. For jobs 1 and 2 alone, the sequence 1–2 has sum of completion times $13+16=29$ and the sequence 2–1 has $13+24=37$; so 1–2 is optimal.
--   2. For all three jobs, the sequence 3–2–1 has sum of completion times
--   $$
--   9+14+25=48,
--   $$
--   and no full sequence has a smaller sum; so 3–2–1 is optimal and reverses the relative order of jobs 1 and 2.
--
--   The paper uses the example to explain why the solution of an $(n-1)$-job subproblem helps little with the $n$-job problem.
--
--   **Formalization Note** Jobs are 0-based in Lean: the paper's jobs 1, 2, 3 are 0, 1, 2. The sequence 3–2–1 is the permutation $\sigma=(0\ 2)$ (positions 0, 1, 2 hold jobs 2, 1, 0) and 2–1 on two jobs is $(0\ 1)$.
-- source:
--   Ignall and Schrage, Application of the branch and bound technique to some flow-shop scheduling problems, Oper. Res. 13 (1965), p. 408, "Computational Results for M=2, Mean Completion Time", 3-job example

import Mathlib
import Definitions.Def_IgnallSchrage_MeanCompletion_Node

namespace IgnallSchrage.MeanCompletion

/-- p. 408, the 3-job example with `a = (2, 10, 1)`, `b = (11, 3, 8)` (jobs `1, 2, 3` of the
paper are `0, 1, 2` here). (i) For jobs 1 and 2 alone, the sequence 1–2 has sum of completion
times `29`, the sequence 2–1 has `37`, so 1–2 is optimal. (ii) For all three jobs, the
sequence 3–2–1 (`σ = (0 2)`: positions `0, 1, 2` hold jobs `2, 1, 0`) has sum `48` and is
optimal among all full sequences. -/
theorem example_p408 :
    (totalCompletion (n := 2) ![2, 10] ![11, 3] 1 = 29 ∧
      totalCompletion (n := 2) ![2, 10] ![11, 3] (Equiv.swap 0 1) = 37 ∧
      ∀ σ : Equiv.Perm (Fin 2),
        totalCompletion (n := 2) ![2, 10] ![11, 3] 1 ≤ totalCompletion ![2, 10] ![11, 3] σ) ∧
    (totalCompletion (n := 3) ![2, 10, 1] ![11, 3, 8] (Equiv.swap 0 2) = 48 ∧
      ∀ σ : Equiv.Perm (Fin 3),
        totalCompletion (n := 3) ![2, 10, 1] ![11, 3, 8] (Equiv.swap 0 2) ≤
          totalCompletion ![2, 10, 1] ![11, 3, 8] σ) := by sorry

end IgnallSchrage.MeanCompletion
