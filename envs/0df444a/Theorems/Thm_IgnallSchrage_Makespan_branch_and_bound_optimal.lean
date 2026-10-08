-- Prove2me | Theorems.Thm_IgnallSchrage_Makespan_branch_and_bound_optimal
-- name    : IgnallSchrage.Makespan.branch_and_bound_optimal
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T12:31:58.910971+00:00
-- url     : https://prove2.me/theorems/5ab8e1fa-1514-4338-918c-b99c3ceb8269
-- title:
--   p. 402 — branch and bound with the bound of p. 401 stops, and its sequence minimizes the makespan
-- statement:
--   Let $n\ge1$ jobs have real processing times $a_i,b_i,c_i$ on machines $A,B,C$, and run the branch-and-bound procedure of p. 402 with the lower bound $LB$ of p. 401. Then:
--
--   1. **Termination.** For some number of steps $k$, the first node of the list $\mathrm{run}(k)$ is terminal (has scheduled $n-1$ jobs).
--   2. **Optimality.** Whenever the first node $P$ of $\mathrm{run}(k)$ is terminal, the full sequence $\sigma^*$ that begins with $P$ (that is, $P$ followed by its one unscheduled job) satisfies
--   $$
--   \mathrm{makespan}(\sigma^*)\ \le\ \mathrm{makespan}(\sigma)\qquad\text{for every permutation }\sigma\text{ of the }n\text{ jobs.}
--   $$
--
--   This is the paper's stopping rule: "The first time that a node that has scheduled all $n$ jobs is first on the list, the problem is solved: that node's sequence is an optimal one." It is the correctness theorem of the Ignall–Schrage algorithm for the three-machine permutation flow shop.
--
--   **Formalization Note** "The problem is solved" is made explicit as termination (part 1) together with optimality over all $n!$ permutations (part 2), not only over the nodes the run created. A node is terminal at depth $n-1$, whose sequence is completed by the forced last job (see the procedure's definition for why the paper forces this reading). Part 2 is stated for every $k$ with a terminal first node, not only the first: once the first node is terminal the procedure leaves the list unchanged. The children of a node are inserted one at a time in increasing job index with the paper's tie rule, but the statement holds for this deterministic rule and its proof does not rely on how ties are broken. No sign condition on processing times is assumed.
-- source:
--   Ignall and Schrage, Application of the branch and bound technique to some flow-shop scheduling problems, Oper. Res. 13 (1965), p. 402, "The Branch-and-Bound Technique", stopping rule, with the lower bound of p. 401

import Mathlib
import Definitions.Def_IgnallSchrage_Makespan_LowerBound
import Definitions.Def_IgnallSchrage_Makespan_Procedure

namespace IgnallSchrage.Makespan

/-- p. 402, stopping rule, with the bound of p. 401: for `n ≥ 1` jobs and any real processing
times, (i) the branch-and-bound run reaches a list whose first node is terminal, and (ii)
whenever the first node `P` of the list is terminal, `P` is the beginning of a full sequence
`σ*` (namely `P` followed by its one unscheduled job) whose makespan is at most the makespan of
every one of the `n!` sequences. -/
theorem branch_and_bound_optimal {n : ℕ} (hn : 1 ≤ n) (a b c : Fin n → ℝ) :
    (∃ k P, (run (lowerBound a b c) k).head? = some P ∧ IsTerminal P) ∧
    ∀ k P, (run (lowerBound a b c) k).head? = some P → IsTerminal P →
      ∃ σstar : Equiv.Perm (Fin n), BeginsWith σstar P ∧
        ∀ σ : Equiv.Perm (Fin n), makespan a b c σstar ≤ makespan a b c σ := by sorry

end IgnallSchrage.Makespan
