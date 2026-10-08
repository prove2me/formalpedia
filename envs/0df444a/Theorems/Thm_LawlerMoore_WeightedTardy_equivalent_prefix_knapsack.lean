-- Prove2me | Theorems.Thm_LawlerMoore_WeightedTardy_equivalent_prefix_knapsack
-- name    : LawlerMoore.WeightedTardy.equivalent_prefix_knapsack
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T13:29:15.76591+00:00
-- url     : https://prove2.me/theorems/3b34e5ae-009e-4b6e-8c37-9e83713e6bac
-- title:
--   Section 6 — minimizing the weighted number of tardy jobs is equivalent to the prefix-constrained knapsack
-- statement:
--   Let $n$ jobs on a single machine have nonnegative integer processing times $a'_j$, nonnegative integer deadlines numbered so that
--   $$
--   d_1 \le d_2 \le \cdots \le d_n,
--   $$
--   and penalties $p_j \ge 0$. Let $W(\sigma)$ be the weighted number of tardy jobs of a sequence $\sigma$, and call a 0–1 vector $x$ prefix-feasible if $a'_1 x_1 + \cdots + a'_k x_k \le d_k$ for $k = 1, \dots, n$. Then
--   1. for every sequence $\sigma$ of the jobs there is a prefix-feasible $x$ with $\sum_j p_j - \sum_j p_j x_j \le W(\sigma)$, and
--   2. for every prefix-feasible $x$ there is a sequence $\sigma$ with $W(\sigma) \le \sum_j p_j - \sum_j p_j x_j$.
--
--   Consequently the minimum of $W$ over all sequences equals $\sum_j p_j$ minus the maximum of $\sum_j p_j x_j$ over prefix-feasible $x$: the weighted-tardy-jobs problem of Section 5 is equivalent to the knapsack-type problem
--   $$
--   \max \sum_{j=1}^n p_j x_j \quad\text{s.t.}\quad a'_1 x_1 + \cdots + a'_k x_k \le d_k \ (k = 1, \dots, n), \quad x_j \in \{0, 1\}.
--   $$
--
--   **Formalization Note** The paper says the two problems are "equivalent" after "a little manipulation"; this is made explicit as the two inequalities above, which together say the optimal values correspond. The deadline numbering ("ordering the jobs by deadlines", Section 5) is the hypothesis `Monotone d` on the job index; the penalties are nonnegative. Both are needed: without either, the equivalence fails on small instances.
-- source:
--   Lawler, Moore, A Functional Equation and Its Application to Resource Allocation and Sequencing Problems, Management Sci. 16 (1969), p. 80, Section 6

import Mathlib
import Definitions.Def_MooreLateJobs_Shared_completionTime
import Definitions.Def_MooreLateJobs_NumLate_lateSet
import Definitions.Def_LawlerMoore_WeightedTardy_weightedTardy
import Definitions.Def_LawlerMoore_WeightedTardy_PrefixFeasible

namespace LawlerMoore.WeightedTardy

open MooreLateJobs.Shared

/-- §6 (p. 80): with the jobs numbered by deadline (`d` monotone) and penalties `p j ≥ 0`, the
problem of §5 is equivalent to the prefix-constrained knapsack problem: every sequence is matched
by a feasible `x` with `∑ p_j - ∑ p_j x_j` at most its weighted number of tardy jobs, and every
feasible `x` is matched by a sequence whose weighted number of tardy jobs is at most
`∑ p_j - ∑ p_j x_j`. -/
theorem equivalent_prefix_knapsack {n : ℕ} (a' d : Fin n → ℕ) (p : Fin n → ℝ)
    (hp : ∀ j, 0 ≤ p j) (hd : Monotone d) :
    (∀ l : List (Fin n), IsSchedule Finset.univ l →
      ∃ x : Fin n → Bool, PrefixFeasible a' d x ∧
        (∑ j, p j) - knapValue p x ≤ weightedTardy a' d p l) ∧
    (∀ x : Fin n → Bool, PrefixFeasible a' d x →
      ∃ l : List (Fin n), IsSchedule Finset.univ l ∧
        weightedTardy a' d p l ≤ (∑ j, p j) - knapValue p x) := by sorry

end LawlerMoore.WeightedTardy
