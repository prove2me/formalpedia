-- Prove2me | Theorems.Thm_IgnallSchrage_Makespan_dominance_lowerBound_le
-- name    : IgnallSchrage.Makespan.dominance_lowerBound_le
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T12:31:16.549914+00:00
-- url     : https://prove2.me/theorems/3f3f47a9-6bbf-4d47-9fb4-fe6644c66c96
-- title:
--   p. 404 — a node cannot dominate a node with a smaller lower bound
-- statement:
--   Let $J_r$ and $I_r$ be two sequences of the same $r$ jobs with $\mathrm{TIMEB}(J_r)\le\mathrm{TIMEB}(I_r)$ and $\mathrm{TIMEC}(J_r)\le\mathrm{TIMEC}(I_r)$, i.e. $J_r$ dominates $I_r$. Then
--
--   $$
--   LB(J_r)\ \le\ LB(I_r).
--   $$
--
--   Equivalently, as the paper puts it, $I_r$ cannot dominate a node with a smaller lower bound. This is why, when a new node is inserted, only the nodes ahead of it on the list need to be checked for dominating it.
--
--   **Formalization Note** "Containing the same $r$ jobs" is encoded as `List.Perm`. No restriction on $r$ is needed: the unscheduled sets of $J_r$ and $I_r$ coincide.
-- source:
--   Ignall and Schrage, Application of the branch and bound technique to some flow-shop scheduling problems, Oper. Res. 13 (1965), p. 404, "Dominated Nodes", "(It should be clear that I_r cannot dominate a node with a smaller lower bound.)"

import Mathlib
import Definitions.Def_IgnallSchrage_Makespan_LowerBound

namespace IgnallSchrage.Makespan

/-- p. 404: if `J` dominates `I` (the same jobs, `TIMEB(J) ≤ TIMEB(I)`, `TIMEC(J) ≤ TIMEC(I)`),
then `LB(J) ≤ LB(I)`; equivalently, a node cannot dominate a node with a smaller lower bound. -/
theorem dominance_lowerBound_le {n : ℕ} (a b c : Fin n → ℝ) (J I : List (Fin n))
    (hJI : J.Perm I) (hB : (times a b c J).2.1 ≤ (times a b c I).2.1)
    (hC : (times a b c J).2.2 ≤ (times a b c I).2.2) :
    lowerBound a b c J ≤ lowerBound a b c I := by sorry

end IgnallSchrage.Makespan
