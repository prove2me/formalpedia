-- Prove2me | Theorems.Thm_IgnallSchrage_MeanCompletion_tval_eq_that_of_sorted
-- name    : IgnallSchrage.MeanCompletion.tval_eq_that_of_sorted
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T17:32:58.482953+00:00
-- url     : https://prove2.me/theorems/360cda1f-75c4-43fd-941e-5d561b81d9d4
-- title:
--   p. 406 — ordering $\bar J_r$ by increasing $a_i$ attains $\hat T_r$
-- statement:
--   Let $J_r$ be a node and $(i_1,\dots,i_{n-r})$ an ordering of $\bar J_r$ with
--   $$
--   a_{i_1}\le a_{i_2}\le\cdots\le a_{i_{n-r}}.
--   $$
--   Then $T_r(i_1,\dots,i_{n-r})=\hat T_r$, the minimum of $T_r$ over all orderings of $\bar J_r$.
--
--   This makes $\hat T_r$ computable by a sort instead of a minimization over $(n-r)!$ orderings.
--
--   **Formalization Note** The ordering is a list that is a permutation of the list of the jobs of $\bar J_r$; "sorted" is `List.Pairwise (fun i j => a i ≤ a j)`. The statement holds for any node, including the root.
-- source:
--   Ignall and Schrage, Application of the branch and bound technique to some flow-shop scheduling problems, Oper. Res. 13 (1965), p. 406, "Since T_r=constant+Σ_p (n−r−p+1)a_{i_p}, …"

import Mathlib
import Definitions.Def_IgnallSchrage_MeanCompletion_LowerBound

namespace IgnallSchrage.MeanCompletion

/-- p. 406: an ordering `(i_1, …, i_{n-r})` of `J̄_r` with `a_{i_1} ≤ a_{i_2} ≤ ⋯ ≤ a_{i_{n-r}}`
attains the minimum `T̂_r` of `T_r` over all orderings of `J̄_r`. -/
theorem tval_eq_that_of_sorted {n : ℕ} (a b : Fin n → ℝ) (J : List (Fin n))
    (l : List (Fin n)) (hl : l ∈ orderings J) (hsort : l.Pairwise (fun i j => a i ≤ a j)) :
    Tval a b J l = That a b J := by sorry

end IgnallSchrage.MeanCompletion
