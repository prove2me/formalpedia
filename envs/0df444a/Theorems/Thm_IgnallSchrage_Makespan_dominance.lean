-- Prove2me | Theorems.Thm_IgnallSchrage_Makespan_dominance
-- name    : IgnallSchrage.Makespan.dominance
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T12:17:39.927173+00:00
-- url     : https://prove2.me/theorems/89544a93-fd1c-430e-bc95-98938b1a79c6
-- title:
--   pp. 403–404 — a dominating partial sequence can replace the dominated one at the beginning of any schedule
-- statement:
--   Let $J_r$ and $I_r$ be two sequences of the same $r$ jobs (one a rearrangement of the other). Then:
--
--   1. $\mathrm{TIMEA}(J_r)=\mathrm{TIMEA}(I_r)$;
--   2. if moreover $\mathrm{TIMEB}(J_r)\le\mathrm{TIMEB}(I_r)$ and $\mathrm{TIMEC}(J_r)\le\mathrm{TIMEC}(I_r)$ ("$J_r$ dominates $I_r$"), then for every full sequence $\sigma$ beginning with $I_r$, the full sequence $\sigma'$ that processes $J_r$ first and then the remaining jobs in the same order as $\sigma$ satisfies
--   $$
--   \mathrm{makespan}(\sigma')\ \le\ \mathrm{makespan}(\sigma).
--   $$
--
--   This is what the paper means by "any schedule which contains $I_r$ at the beginning cannot be hurt by replacing $I_r$ with $J_r$", and it justifies discarding a dominated node without losing an optimal sequence.
--
--   **Formalization Note** The comparison is between completions of $J_r$ and $I_r$ by the same ordering of the remaining jobs. The paper's "two different sequences" is not required: for $J_r=I_r$ the statement is trivially true. "Containing the same $r$ jobs" is encoded as `List.Perm`. No sign condition on processing times is assumed.
-- source:
--   Ignall and Schrage, Application of the branch and bound technique to some flow-shop scheduling problems, Oper. Res. 13 (1965), pp. 403–404, "Dominated Nodes"

import Mathlib
import Definitions.Def_IgnallSchrage_Makespan_Node

namespace IgnallSchrage.Makespan

/-- pp. 403–404, dominated nodes: let `J` and `I` be two sequences of the same `r` jobs. Then
`TIMEA(J) = TIMEA(I)`; and if `TIMEB(J) ≤ TIMEB(I)` and `TIMEC(J) ≤ TIMEC(I)`, every full
sequence `σ` beginning with `I` is not improved upon by replacing `I` by `J`: the full sequence
`σ'` that runs `J` and then the remaining jobs in the same order as `σ` has makespan at most
that of `σ`. -/
theorem dominance {n : ℕ} (a b c : Fin n → ℝ) (J I : List (Fin n)) (hJI : J.Perm I) :
    (times a b c J).1 = (times a b c I).1 ∧
    ((times a b c J).2.1 ≤ (times a b c I).2.1 → (times a b c J).2.2 ≤ (times a b c I).2.2 →
      ∀ σ σ' : Equiv.Perm (Fin n), BeginsWith σ I →
        List.ofFn σ' = J ++ (List.ofFn σ).drop I.length →
        makespan a b c σ' ≤ makespan a b c σ) := by sorry

end IgnallSchrage.Makespan
