-- Prove2me | Theorems.Thm_McNaughtonSched_SingleProc_split_reduction
-- name    : McNaughtonSched.SingleProc.split_reduction
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T15:00:23.055863+00:00
-- url     : https://prove2.me/theorems/2ed3097e-bacb-4908-b214-03edc8625926
-- title:
--   Proof of Theorem 2.2 — a schedule with $\sum s_i > m$ parts can be improved to fewer parts
-- statement:
--   Consider $m$ tasks on a single processor with processing times $a_i > 0$, penalties $p_i \ge 0$ and deadlines $d_i$, and let $c(S)$ be the total loss of a schedule $S$. Write $s_i$ for the number of parts into which task $(i)$ is split in $S$, so that $\sum_{i=1}^m s_i$ is the total number of pieces of $S$. If $S$ is feasible and
--
--   $$
--   \sum_{i=1}^m s_i > m,
--   $$
--
--   then there is a feasible schedule $S'$ with strictly fewer pieces than $S$ and no greater loss, $c(S') \le c(S)$.
--
--   This is the reduction step in the proof of Theorem 2.2: iterating it removes all splits without increasing the loss.
--
--   **Formalization Note** $\sum_i s_i$ is the length of the list of pieces. Since every feasible schedule gives each task its $a_i > 0$ units, every task has at least one piece, so $\sum_i s_i > m$ says exactly that some task is split. The penalty hypothesis $p_i \ge 0$ is what makes "finished sooner or at the same time" imply "no greater loss".
-- source:
--   McNaughton, Scheduling with Deadlines and Loss Functions, Management Science 6(1), 1959, pp. 4–5, proof of Theorem 2.2 (p. 5, first sentence)

import Mathlib
import Definitions.Def_McNaughtonSched_SingleProc_Model

namespace McNaughtonSched.SingleProc

theorem split_reduction {m : ℕ} (a p d : Fin m → ℝ)
    (ha : ∀ i, 0 < a i) (hp : ∀ i, 0 ≤ p i)
    (S : Schedule m) (hS : IsFeasible a S) (hsplit : m < S.length) :
    ∃ S' : Schedule m, IsFeasible a S' ∧ S'.length < S.length ∧
      totalLoss p d S' ≤ totalLoss p d S := by sorry

end McNaughtonSched.SingleProc
