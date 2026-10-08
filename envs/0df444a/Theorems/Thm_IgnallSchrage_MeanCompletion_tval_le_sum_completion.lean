-- Prove2me | Theorems.Thm_IgnallSchrage_MeanCompletion_tval_le_sum_completion
-- name    : IgnallSchrage.MeanCompletion.tval_le_sum_completion
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T17:33:16.754257+00:00
-- url     : https://prove2.me/theorems/37ba228f-a3fa-4163-b76f-fc9e80c6f000
-- title:
--   pp. 405–406 — the sum of completion times over $\bar J_r$ is at least $T_r$ of its order, hence at least $\hat T_r$
-- statement:
--   Let $1\le r\le n-1$, let $J_r$ be a node and let $\sigma$ be any full sequence that begins with $J_r$. Let $(i_1,\dots,i_{n-r})$ be the order in which $\sigma$ processes the jobs of $\bar J_r$, and let $d_i(\sigma)$ be the completion times of $\sigma$ on machine $B$. Then
--   $$
--   T_r(i_1,\dots,i_{n-r})\ \le\ \sum_{i\in\bar J_r}d_i(\sigma)
--   \qquad\text{and}\qquad
--   \hat T_r\ \le\ \sum_{i\in\bar J_r}d_i(\sigma).
--   $$
--
--   $T_r$ is the value the sum would have if no job of $\bar J_r$ waited for machine $B$; delays can only increase the actual sum. This is the first half of the bound $LB(J_r)$.
--
--   **Formalization Note** The paper writes that with delays "the actual sum of completion times will exceed $T_r$"; the statement makes this the non-strict inequality $\le$, with equality when no delay occurs. The barred $\bar J_r$ under the paper's "$\sum_{J_r} d_i$" on p. 406 is invisible in the scan; the sum is over $\bar J_r$, as the paper's p. 405 decomposition into $\sum_{i\in J_r}d_i+\sum_{i\in\bar J_r}d_i$ requires.
-- source:
--   Ignall and Schrage, Application of the branch and bound technique to some flow-shop scheduling problems, Oper. Res. 13 (1965), pp. 405–406, "M=2; A Lower Bound on Mean Completion Time for All Nodes Emanating from a Given Node", T_r and "the minimum possible value for T_r, call it T̂_r, is a lower bound"

import Mathlib
import Definitions.Def_IgnallSchrage_MeanCompletion_LowerBound

namespace IgnallSchrage.MeanCompletion

/-- pp. 405–406: for a node `J = J_r` with `1 ≤ r ≤ n - 1` and every full sequence `σ` that
begins with `J`, let `l = (i_1, …, i_{n-r})` be the order in which `σ` processes `J̄_r` (the
positions after the first `r`). Then `T_r(l) ≤ Σ_{i ∈ J̄_r} d_i(σ)`, and hence
`T̂_r ≤ Σ_{i ∈ J̄_r} d_i(σ)`. -/
theorem tval_le_sum_completion {n : ℕ} (a b : Fin n → ℝ) (J : List (Fin n))
    (hr : 1 ≤ J.length) (hrn : J.length < n) (σ : Equiv.Perm (Fin n)) (hσ : IgnallSchrage.Makespan.BeginsWith σ J) :
    Tval a b J ((List.ofFn σ).drop J.length) ≤ ∑ i ∈ IgnallSchrage.Makespan.unscheduled J, completionTime a b σ i ∧
    That a b J ≤ ∑ i ∈ IgnallSchrage.Makespan.unscheduled J, completionTime a b σ i := by sorry

end IgnallSchrage.MeanCompletion
