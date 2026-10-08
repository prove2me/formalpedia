-- Prove2me | Theorems.Thm_LawlerPrec_MinMax_move_last_feasible
-- name    : LawlerPrec.MinMax.move_last_feasible
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-04T19:14:21.233147+00:00
-- url     : https://prove2.me/theorems/7b56b156-30ec-41d2-802c-448d130e612b
-- title:
--   §2, proof of the Theorem, p. 544 — moving a job of $S$ to the end keeps the precedence constraints
-- statement:
--   Let $\pi'$ be a sequence of the job set $J$ that observes the precedence constraints, and let $k \in S(J)$ be a job that is not required to precede any other job of $J$. Let $\pi$ be obtained from $\pi'$ by removing $k$ and appending it at the end. Then
--
--   $$
--   \pi' \text{ observes the precedence constraints} \;\Longrightarrow\; \pi \text{ observes them.}
--   $$
--
--   In Lawler's proof $\pi' = (A, k, B, k')$ and $\pi = (A, B, k', k)$; this is the first of the three steps showing that moving $k$ to the last position never hurts.
--
--   **Formalization Note** $\pi$ is written `l.erase k ++ [k]` for $\pi' =$ `l`, which is the page's $(A, B, k', k)$ whenever `l = A ++ [k] ++ B ++ [k']`, and covers also the case where $k$ is already last.
-- source:
--   Lawler, Optimal Sequencing of a Single Machine Subject to Precedence Constraints, Management Science 19(5), 1973, p. 544, §2 Sequencing Theorem, PROOF, third paragraph

import Mathlib
import Definitions.Def_LawlerPrec_MinMax_IsFeasible
import Definitions.Def_LawlerPrec_MinMax_lastEligible

namespace LawlerPrec.MinMax

/-- §2, proof of the Theorem, p. 544, third paragraph: moving a job `k ∈ S` to the last position
of a sequence `π′ = l` that observes the precedence constraints gives a sequence
`π = l.erase k ++ [k]` that observes them too. When `l = A ++ [k] ++ B ++ [k′]` this `π` is the
page's `A ++ B ++ [k′] ++ [k]`. -/
theorem move_last_feasible {ι : Type*} [DecidableEq ι] (prec : ι → ι → Prop) (J : Finset ι)
    (l : List ι) (k : ι) (hl : IsFeasible prec J l) (hk : k ∈ lastEligible prec J) :
    IsFeasible prec J (l.erase k ++ [k]) := by sorry

end LawlerPrec.MinMax
