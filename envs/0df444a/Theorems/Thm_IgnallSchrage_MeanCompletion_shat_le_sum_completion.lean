-- Prove2me | Theorems.Thm_IgnallSchrage_MeanCompletion_shat_le_sum_completion
-- name    : IgnallSchrage.MeanCompletion.shat_le_sum_completion
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T17:33:26.492983+00:00
-- url     : https://prove2.me/theorems/af9df94c-3964-42d6-be60-ecd783bf0e38
-- title:
--   p. 406 — the sum of completion times over $\bar J_r$ is at least $S_r$ of its order, hence at least $\hat S_r$
-- statement:
--   Let $1\le r\le n-1$, let $J_r$ be a node and let $\sigma$ be any full sequence that begins with $J_r$. Let $(j_1,\dots,j_{n-r})$ be the order in which $\sigma$ processes the jobs of $\bar J_r$, and let $d_i(\sigma)$ be the completion times of $\sigma$ on machine $B$. Then
--   $$
--   S_r(j_1,\dots,j_{n-r})\ \le\ \sum_{i\in\bar J_r}d_i(\sigma)
--   \qquad\text{and}\qquad
--   \hat S_r\ \le\ \sum_{i\in\bar J_r}d_i(\sigma).
--   $$
--
--   This is the second half of the bound $LB(J_r)$, and it holds whether or not machine $B$ dominates.
--
--   **Formalization Note** The paper first describes $S_r$ as "the sum of the completion times for the jobs in $\bar J_r$" when $\min_{\bar J_r}b_i\ge\max_{\bar J_r}a_i$. That description is not formalized as an equality: $S_r$ uses $\min_{\bar J_r}a_i$ in place of $a_{j_1}$, so even under the condition the actual sum may exceed $S_r$. What the paper uses, and what is stated, is the lower bound ("the actual sum of completion times will be $\ge\hat S_r$, no matter how the jobs in $\bar J_r$ are sequenced"). The bars over $\bar J_r$ in the subscripts of $\min$ and $\max$ are invisible in the scan.
-- source:
--   Ignall and Schrage, Application of the branch and bound technique to some flow-shop scheduling problems, Oper. Res. 13 (1965), p. 406, "In the same way as with T_r, it should be evident that if the condition does not hold, the actual sum of completion times will be ≧Ŝ_r"

import Mathlib
import Definitions.Def_IgnallSchrage_MeanCompletion_LowerBound

namespace IgnallSchrage.MeanCompletion

/-- p. 406: for a node `J = J_r` with `1 ≤ r ≤ n - 1` and every full sequence `σ` that begins
with `J`, whatever the order `l` in which `σ` processes `J̄_r`, `S_r(l) ≤ Σ_{i ∈ J̄_r} d_i(σ)`,
and hence `Ŝ_r ≤ Σ_{i ∈ J̄_r} d_i(σ)`. -/
theorem shat_le_sum_completion {n : ℕ} (a b : Fin n → ℝ) (J : List (Fin n))
    (hr : 1 ≤ J.length) (hrn : J.length < n) (σ : Equiv.Perm (Fin n)) (hσ : IgnallSchrage.Makespan.BeginsWith σ J) :
    Sval a b J ((List.ofFn σ).drop J.length) ≤ ∑ i ∈ IgnallSchrage.Makespan.unscheduled J, completionTime a b σ i ∧
    Shat a b J ≤ ∑ i ∈ IgnallSchrage.Makespan.unscheduled J, completionTime a b σ i := by sorry

end IgnallSchrage.MeanCompletion
