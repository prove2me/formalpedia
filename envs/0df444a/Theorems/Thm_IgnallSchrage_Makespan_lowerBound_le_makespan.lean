-- Prove2me | Theorems.Thm_IgnallSchrage_Makespan_lowerBound_le_makespan
-- name    : IgnallSchrage.Makespan.lowerBound_le_makespan
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T12:30:59.157182+00:00
-- url     : https://prove2.me/theorems/048b367c-f026-4315-a825-ffe75a3da5f8
-- title:
--   p. 401 — $LB(J_r)$ is a lower bound on the makespan of every sequence that begins with $J_r$
-- statement:
--   Let $n$ jobs have real processing times $a_i,b_i,c_i$ on machines $A,B,C$. Let $J_r$ be a node with $r<n$ jobs, so that its unscheduled set $\bar J_r$ is nonempty, and let $\sigma$ be any full sequence that begins with $J_r$. Then
--
--   $$
--   LB(J_r)\ \le\ \mathrm{makespan}(\sigma).
--   $$
--
--   In the paper's words, $LB(P)=LB(J_r)$ is a lower bound on the makespan for any node that emanates from node $P$, since all such nodes represent sequences that begin with $J_r$. This is the property that makes $LB$ a valid ranking key for branch and bound: no completion of a node can beat the node's bound.
--
--   **Formalization Note** "Any node that emanates from $P$" is made explicit as every permutation $\sigma$ whose first $r$ positions are $J_r$. The paper's nodes have $1$ to $n$ jobs; the statement also covers the root ($r=0$). No sign condition on the processing times is assumed.
-- source:
--   Ignall and Schrage, Application of the branch and bound technique to some flow-shop scheduling problems, Oper. Res. 13 (1965), p. 401, "A Lower Bound for the Makespan of All Nodes Emanating from a Given Node", LB(P) is a lower bound

import Mathlib
import Definitions.Def_IgnallSchrage_Makespan_LowerBound

namespace IgnallSchrage.Makespan

/-- p. 401: for a node `J = J_r` with `r < n` (so that `J̄_r` is nonempty), `LB(J_r)` is at most
the makespan of every full sequence `σ` that begins with `J_r`. -/
theorem lowerBound_le_makespan {n : ℕ} (a b c : Fin n → ℝ) (J : List (Fin n))
    (hJ : J.length < n) (σ : Equiv.Perm (Fin n)) (hσ : BeginsWith σ J) :
    lowerBound a b c J ≤ makespan a b c σ := by sorry

end IgnallSchrage.Makespan
