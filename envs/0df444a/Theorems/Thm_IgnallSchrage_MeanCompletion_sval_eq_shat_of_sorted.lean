-- Prove2me | Theorems.Thm_IgnallSchrage_MeanCompletion_sval_eq_shat_of_sorted
-- name    : IgnallSchrage.MeanCompletion.sval_eq_shat_of_sorted
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T17:33:56.210552+00:00
-- url     : https://prove2.me/theorems/65268de3-6f7e-4844-8759-ae3887fa0bf0
-- title:
--   p. 406 — ordering $\bar J_r$ by increasing $b_j$ attains $\hat S_r$
-- statement:
--   Let $J_r$ be a node and $(j_1,\dots,j_{n-r})$ an ordering of $\bar J_r$ with
--   $$
--   b_{j_1}\le b_{j_2}\le\cdots\le b_{j_{n-r}}.
--   $$
--   Then $S_r(j_1,\dots,j_{n-r})=\hat S_r$, the minimum of $S_r$ over all orderings of $\bar J_r$.
--
--   Together with the previous statement, this makes $LB(J_r)$ computable with two sorts.
--
--   **Formalization Note** The ordering is a list that is a permutation of the list of the jobs of $\bar J_r$; "sorted" is `List.Pairwise (fun i j => b i ≤ b j)`. The statement holds for any node, including the root.
-- source:
--   Ignall and Schrage, Application of the branch and bound technique to some flow-shop scheduling problems, Oper. Res. 13 (1965), p. 406, "S_r=constant+Σ_{p=1}^{n−r}(n−r−p+1)b_{j_p} so it is clear that choosing a sequence so that b_{j_1}≦⋯≦b_{j_{n−r}} will minimize S_r"

import Mathlib
import Definitions.Def_IgnallSchrage_MeanCompletion_LowerBound

namespace IgnallSchrage.MeanCompletion

/-- p. 406: an ordering `(j_1, …, j_{n-r})` of `J̄_r` with `b_{j_1} ≤ b_{j_2} ≤ ⋯ ≤ b_{j_{n-r}}`
attains the minimum `Ŝ_r` of `S_r` over all orderings of `J̄_r`. -/
theorem sval_eq_shat_of_sorted {n : ℕ} (a b : Fin n → ℝ) (J : List (Fin n))
    (l : List (Fin n)) (hl : l ∈ orderings J) (hsort : l.Pairwise (fun i j => b i ≤ b j)) :
    Sval a b J l = Shat a b J := by sorry

end IgnallSchrage.MeanCompletion
