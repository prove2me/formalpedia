-- Prove2me | Theorems.Thm_IgnallSchrage_MeanCompletion_lowerBound_eq_totalCompletion_of_terminal
-- name    : IgnallSchrage.MeanCompletion.lowerBound_eq_totalCompletion_of_terminal
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T17:33:39.551991+00:00
-- url     : https://prove2.me/theorems/c5e39a39-6735-4de2-8d24-2d90490b1075
-- title:
--   Exactness of $LB$ at depth $n-1$ (needed by the stopping rule, p. 402)
-- statement:
--   Let $J_{n-1}$ be a node that has scheduled $n-1$ of the $n$ jobs, so that $\bar J_{n-1}=\{j\}$ is a single job, and let $\sigma$ be the full sequence $J_{n-1}$ followed by $j$. Then
--   $$
--   LB(J_{n-1})=\sum_{i=1}^{n}d_i(\sigma).
--   $$
--
--   The paper's stopping rule declares a terminal node's sequence optimal as soon as the node is first on the list; that conclusion needs the bound of such a node to be the value of its sequence, which is this statement.
--
--   **Formalization Note** The paper does not state this for two machines; it is the general form of what its stopping rule (p. 402) relies on, and is labelled as such. It holds for arbitrary real processing times and also for $n=1$, where the node is the root (with $d_k$ read as $0$).
-- source:
--   Ignall and Schrage, Application of the branch and bound technique to some flow-shop scheduling problems, Oper. Res. 13 (1965), p. 402, "The Branch-and-Bound Technique", stopping rule (general form needed for the bound of p. 406)

import Mathlib
import Definitions.Def_IgnallSchrage_MeanCompletion_LowerBound

namespace IgnallSchrage.MeanCompletion

/-- Exactness of the bound at depth `n - 1` (needed by the stopping rule of p. 402): if the
node `J` has scheduled `n - 1` of the `n` jobs, then for the (unique) full sequence `σ` that
begins with `J`, `LB(J) = Σ_i d_i(σ)`. -/
theorem lowerBound_eq_totalCompletion_of_terminal {n : ℕ} (a b : Fin n → ℝ)
    (J : List (Fin n)) (hJ : J.length + 1 = n) (σ : Equiv.Perm (Fin n)) (hσ : IgnallSchrage.Makespan.BeginsWith σ J) :
    lowerBound a b J = totalCompletion a b σ := by sorry

end IgnallSchrage.MeanCompletion
