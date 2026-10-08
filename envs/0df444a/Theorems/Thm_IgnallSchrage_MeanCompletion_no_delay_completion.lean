-- Prove2me | Theorems.Thm_IgnallSchrage_MeanCompletion_no_delay_completion
-- name    : IgnallSchrage.MeanCompletion.no_delay_completion
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:34:07.013815+00:00
-- url     : https://prove2.me/theorems/069d7668-59d7-483e-95c6-78f82e99fb6a
-- title:
--   pp. 405–406 — without delays, job $i_p$ completes at $\sum_{J_r}a_j+a_{i_1}+\cdots+a_{i_p}+b_{i_p}$ and the sum over $\bar J_r$ is $T_r$
-- statement:
--   Let $1\le r\le n-1$, let $J_r$ be a node with last job $k$, and let $\sigma$ be a full sequence that begins with $J_r$ and processes $\bar J_r$ in the order $(i_1,\dots,i_{n-r})$. Suppose
--   $$
--   \min_{i\in\bar J_r}a_i\ \ge\ \max_{i\in\bar J_r}b_i
--   \qquad\text{and}\qquad
--   \min_{i\in\bar J_r}a_i\ \ge\ d_k-\sum_{i\in J_r}a_i .
--   $$
--   Then for every $p$ the completion time of job $i_p$ is
--   $$
--   d_{i_p}(\sigma)=\sum_{j\in J_r}a_j+a_{i_1}+\cdots+a_{i_p}+b_{i_p},
--   $$
--   and $\sum_{i\in\bar J_r}d_i(\sigma)=T_r(i_1,\dots,i_{n-r})$.
--
--   This is the case in which machine $A$ dominates: no job of $\bar J_r$ waits for machine $B$, and $T_r$ is attained.
--
--   **Formalization Note** The two conditions on minima and maxima are stated elementwise: $b_j\le a_i$ for all $i,j\in\bar J_r$, and $d_k-\sum_{J_r}a\le a_i$ for all $i\in\bar J_r$. Positions $p$ are 0-based in Lean. The bars over $\bar J_r$ in the subscripts of $\min$ and $\max$ are invisible in the scan.
-- source:
--   Ignall and Schrage, Application of the branch and bound technique to some flow-shop scheduling problems, Oper. Res. 13 (1965), pp. 405–406, "When min_{i∈J̄_r} a_i≧max_{i∈J̄_r} b_i and min_{i∈J̄_r} a_i≧d_k−Σ_{i∈J_r} a_i …"

import Mathlib
import Definitions.Def_IgnallSchrage_MeanCompletion_LowerBound

namespace IgnallSchrage.MeanCompletion

/-- pp. 405–406, the case without delays: let `J = J_r` with `1 ≤ r ≤ n - 1`, `k` its last job,
and `σ` a full sequence beginning with `J` that processes `J̄_r` in the order
`l = (i_1, …, i_{n-r})`. If `min_{i ∈ J̄_r} a_i ≥ max_{i ∈ J̄_r} b_i` and
`min_{i ∈ J̄_r} a_i ≥ d_k - Σ_{i ∈ J_r} a_i`, then the completion time of `i_p` is
`Σ_{j ∈ J_r} a_j + a_{i_1} + ⋯ + a_{i_p} + b_{i_p}`, and `Σ_{i ∈ J̄_r} d_i(σ) = T_r(l)`. -/
theorem no_delay_completion {n : ℕ} (a b : Fin n → ℝ) (J : List (Fin n))
    (hr : 1 ≤ J.length) (hrn : J.length < n) (σ : Equiv.Perm (Fin n)) (hσ : IgnallSchrage.Makespan.BeginsWith σ J)
    (hab : ∀ i ∈ IgnallSchrage.Makespan.unscheduled J, ∀ j ∈ IgnallSchrage.Makespan.unscheduled J, b j ≤ a i)
    (hdk : ∀ i ∈ IgnallSchrage.Makespan.unscheduled J, lastCompletion a b J - (J.map a).sum ≤ a i) :
    let l := (List.ofFn σ).drop J.length
    (∀ p : Fin l.length,
      completionTime a b σ l[p] = (J.map a).sum + ∑ q ∈ Finset.Iic p, a l[q] + b l[p]) ∧
    ∑ i ∈ IgnallSchrage.Makespan.unscheduled J, completionTime a b σ i = Tval a b J l := by sorry

end IgnallSchrage.MeanCompletion
