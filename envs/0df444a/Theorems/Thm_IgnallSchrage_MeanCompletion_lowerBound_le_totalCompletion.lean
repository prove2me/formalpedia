-- Prove2me | Theorems.Thm_IgnallSchrage_MeanCompletion_lowerBound_le_totalCompletion
-- name    : IgnallSchrage.MeanCompletion.lowerBound_le_totalCompletion
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T17:33:32.917749+00:00
-- url     : https://prove2.me/theorems/6bdc9149-bea3-4636-837d-21fed3877fa6
-- title:
--   p. 406 — $LB(J_r)=\sum_{J_r}d_i+\max(\hat T_r,\hat S_r)$ is a lower bound on the sum of completion times
-- statement:
--   Let $1\le r\le n-1$ and let $J_r$ be a node. For every full sequence $\sigma$ that begins with $J_r$,
--   $$
--   LB(J_r)=\sum_{i\in J_r}d_i+\max(\hat T_r,\hat S_r)\ \le\ \sum_{i=1}^{n}d_i(\sigma).
--   $$
--
--   This is the property that lets the branch-and-bound procedure discard, implicitly, all sequences that begin with a node whose bound exceeds the value of a known complete sequence.
--
--   **Formalization Note** "$LB(\cdot)$ is a lower bound" is read as: for every node with $1\le r\le n-1$, and every one of the $(n-r)!$ full sequences beginning with it, $LB$ is at most its sum of completion times. The objective is the sum rather than the mean of the completion times; the two differ by the fixed factor $1/n$.
-- source:
--   Ignall and Schrage, Application of the branch and bound technique to some flow-shop scheduling problems, Oper. Res. 13 (1965), p. 406, "Therefore, LB(J_r)=Σ_{i∈J_r} d_i+max(T̂_r, Ŝ_r) and LB(·) is a lower bound"

import Mathlib
import Definitions.Def_IgnallSchrage_MeanCompletion_LowerBound

namespace IgnallSchrage.MeanCompletion

/-- p. 406: for a node `J = J_r` with `1 ≤ r ≤ n - 1`,
`LB(J_r) = Σ_{i ∈ J_r} d_i + max(T̂_r, Ŝ_r)` is at most the sum of the completion times of
every full sequence that begins with `J_r`. -/
theorem lowerBound_le_totalCompletion {n : ℕ} (a b : Fin n → ℝ) (J : List (Fin n))
    (hr : 1 ≤ J.length) (hrn : J.length < n) (σ : Equiv.Perm (Fin n)) (hσ : IgnallSchrage.Makespan.BeginsWith σ J) :
    lowerBound a b J ≤ totalCompletion a b σ := by sorry

end IgnallSchrage.MeanCompletion
