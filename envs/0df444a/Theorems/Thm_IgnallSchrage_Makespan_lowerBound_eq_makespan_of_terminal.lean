-- Prove2me | Theorems.Thm_IgnallSchrage_Makespan_lowerBound_eq_makespan_of_terminal
-- name    : IgnallSchrage.Makespan.lowerBound_eq_makespan_of_terminal
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T12:32:04.296362+00:00
-- url     : https://prove2.me/theorems/580f12b0-9739-4263-ab67-ef2dc798ab27
-- title:
--   p. 403, An Example — the bound of a node with $n-1$ jobs is the makespan of its completion (general form)
-- statement:
--   Let $J_{n-1}$ be a node with $n-1$ of the $n$ jobs and let $\sigma$ be the full sequence that begins with $J_{n-1}$, i.e. $J_{n-1}$ followed by its one unscheduled job. Then
--
--   $$
--   LB(J_{n-1}) = \mathrm{makespan}(\sigma).
--   $$
--
--   The paper observes this for its example ("node 231's lower bound, which is the makespan for sequence 2314"); this is the general form. It is what turns the bound of a terminal node into the value of an actual sequence, and so lets the stopping rule certify optimality.
--
--   **Formalization Note** The paper states the identity for one node of its example only; the statement here is its general form for any $n\ge1$ and any real processing times.
-- source:
--   Ignall and Schrage, Application of the branch and bound technique to some flow-shop scheduling problems, Oper. Res. 13 (1965), p. 403, An Example, "node 231's lower bound, which is the makespan for sequence 2314" (general form)

import Mathlib
import Definitions.Def_IgnallSchrage_Makespan_LowerBound

namespace IgnallSchrage.Makespan

/-- General form of p. 403 ("node 231's lower bound, which is the makespan for sequence 2314"):
for a node `J = J_{n-1}` with `n - 1` jobs, `LB(J_{n-1})` equals the makespan of the full
sequence `σ` that begins with `J_{n-1}` (i.e. `J_{n-1}` followed by its one unscheduled job). -/
theorem lowerBound_eq_makespan_of_terminal {n : ℕ} (a b c : Fin n → ℝ) (J : List (Fin n))
    (hJ : J.length + 1 = n) (σ : Equiv.Perm (Fin n)) (hσ : BeginsWith σ J) :
    lowerBound a b c J = makespan a b c σ := by sorry

end IgnallSchrage.Makespan
