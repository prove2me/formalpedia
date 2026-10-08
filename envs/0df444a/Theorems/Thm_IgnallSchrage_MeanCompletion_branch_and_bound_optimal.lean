-- Prove2me | Theorems.Thm_IgnallSchrage_MeanCompletion_branch_and_bound_optimal
-- name    : IgnallSchrage.MeanCompletion.branch_and_bound_optimal
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T17:35:14.416661+00:00
-- url     : https://prove2.me/theorems/4606e2fa-cdbc-407d-a78f-3dbfcfb3f356
-- title:
--   p. 402 — branch and bound with the two-machine bound of p. 406 stops at a sequence of least mean completion time
-- statement:
--   Let $n\ge1$ jobs have arbitrary real processing times $a_i$ on machine $A$ and $b_i$ on machine $B$. Run the branch-and-bound procedure of p. 402, ranking nodes by
--   $$
--   LB(J_r)=\sum_{i\in J_r}d_i+\max(\hat T_r,\hat S_r).
--   $$
--   Then:
--
--   1. the procedure stops: after some number $k$ of steps, the first node of the list is terminal (it has scheduled $n-1$ jobs);
--   2. whenever the first node $P$ of the list is terminal, the sequence $\sigma^\ast$ consisting of $P$ followed by its one unscheduled job satisfies
--   $$
--   \sum_{i=1}^{n}d_i(\sigma^\ast)\ \le\ \sum_{i=1}^{n}d_i(\sigma)\qquad\text{for every permutation }\sigma\text{ of the }n\text{ jobs}.
--   $$
--
--   Since $n$ is fixed, $\sigma^\ast$ also minimizes the mean completion time $\frac1n\sum_i d_i$, the paper's objective. This is the correctness of the paper's method for the two-machine mean-completion-time problem.
--
--   **Formalization Note** "The problem is solved: that node's sequence is an optimal one" is read as termination (some $k$) together with optimality over all $n!$ permutation sequences. Terminal nodes are those at depth $n-1$, whose last job is forced, as the paper's example (p. 403) and node counts show. The tie rule is that of p. 403 (a new node precedes old nodes with the same bound); the statement holds for any real data, without a sign condition.
-- source:
--   Ignall and Schrage, Application of the branch and bound technique to some flow-shop scheduling problems, Oper. Res. 13 (1965), p. 402, "The Branch-and-Bound Technique", stopping rule; with the bound of p. 406, "M=2; A Lower Bound on Mean Completion Time for All Nodes Emanating from a Given Node"

import Mathlib
import Definitions.Def_IgnallSchrage_MeanCompletion_LowerBound
import Definitions.Def_IgnallSchrage_Makespan_Procedure

namespace IgnallSchrage.MeanCompletion

/-- p. 402, stopping rule, with the two-machine bound of p. 406: for `n ≥ 1` jobs and any real
processing times, (i) the branch-and-bound IgnallSchrage.Makespan.run ranked by `LB(J_r) = Σ_{J_r} d_i + max(T̂_r, Ŝ_r)`
reaches a list whose first node is terminal, and (ii) whenever the first node `P` of the list
is terminal, `P` is the beginning of a full sequence `σ*` (namely `P` followed by its one
IgnallSchrage.Makespan.unscheduled job) whose sum of completion times is at most that of every one of the `n!`
sequences. -/
theorem branch_and_bound_optimal {n : ℕ} (hn : 1 ≤ n) (a b : Fin n → ℝ) :
    (∃ k P, (IgnallSchrage.Makespan.run (lowerBound a b) k).head? = some P ∧ IgnallSchrage.Makespan.IsTerminal P) ∧
    ∀ k P, (IgnallSchrage.Makespan.run (lowerBound a b) k).head? = some P → IgnallSchrage.Makespan.IsTerminal P →
      ∃ σstar : Equiv.Perm (Fin n), IgnallSchrage.Makespan.BeginsWith σstar P ∧
        ∀ σ : Equiv.Perm (Fin n), totalCompletion a b σstar ≤ totalCompletion a b σ := by sorry

end IgnallSchrage.MeanCompletion
