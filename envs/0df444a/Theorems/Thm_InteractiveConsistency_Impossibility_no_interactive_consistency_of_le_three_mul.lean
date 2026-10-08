-- Prove2me | Theorems.Thm_InteractiveConsistency_Impossibility_no_interactive_consistency_of_le_three_mul
-- name    : InteractiveConsistency.Impossibility.no_interactive_consistency_of_le_three_mul
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T15:36:52.174708+00:00
-- url     : https://prove2.me/theorems/684e502f-53f8-4dae-82d7-1ee74affc19b
-- title:
--   THEOREM (Section 4) — for |V| ≥ 2 and 3 ≤ n ≤ 3m no {F_p} assures interactive consistency for m faults
-- statement:
--   Let $P$ be a finite set of $n$ processors, $V$ a set of values and $m$ a natural number. Suppose that $V$ has at least two elements and that
--   $$3\le n\le 3m.$$
--   Then there is no family $\{F_p\mid p\in P\}$ of decision functions, each $F_p$ taking the $p$-scenario $\sigma_p$ and a processor $q$ to a value $F_p(\sigma_p, q)\in V$, that assures interactive consistency for $m$ faults.
--
--   In words: when a third or more of the processors may be faulty, no protocol — however many rounds of message exchange it uses — lets every nonfaulty processor compute the true private value of every nonfaulty processor and lets all nonfaulty processors agree on the whole vector. Together with the algorithm of Section 3 for $n\ge 3m+1$, it shows that $n\ge 3m+1$ is exactly the condition for interactive consistency with oral (unauthenticated) messages.
--
--   **Formalization Note** The paper prints the hypothesis as "$n\ge 3m$". This is a misprint: the proof begins "Since $n\le 3m$", the section is titled "Proof of Impossibility for $n<3m+1$", and with $n\ge 3m$ the statement is false (Section 3 solves $n=4$, $m=1$). The hypothesis $n\ge 3$, used in the proof to split $P$ into three nonempty sets, is made explicit; without it the statement is false (for $n\le 2$, $F_p(\sigma_p,q)=\sigma(pq)$ assures interactive consistency). $|V|\ge2$ is written as the existence of two distinct values. Decision functions see only $w\mapsto\sigma(pw)$; scenarios are defined on strings of every length.
-- source:
--   Pease, Shostak & Lamport, Reaching agreement in the presence of faults, J. ACM 27 (1980), p. 232, THEOREM (Section 4); proof pp. 232–233

import Mathlib
import Definitions.Def_InteractiveConsistency_Impossibility_Scenario

namespace InteractiveConsistency.Impossibility

/-- Pease, Shostak & Lamport (1980), Section 4, THEOREM, p. 232 (with the printed hypothesis
`n ≥ 3m` corrected to `n ≤ 3m`, as the proof and the section title require, and with the implicit
`n ≥ 3` of the proof made explicit): if `|V| ≥ 2` and `3 ≤ n ≤ 3m`, where `n = |P|`, there exists no
family `{F_p | p ∈ P}` that assures interactive consistency for `m` faults. -/
theorem no_interactive_consistency_of_le_three_mul {α V : Type*} [DecidableEq α]
    (P : Finset α) (m : ℕ) (hV : ∃ v v' : V, v ≠ v')
    (h3 : 3 ≤ P.card) (hn : P.card ≤ 3 * m) :
    ∀ F : α → (List α → V) → α → V, ¬ AssuresIC P m F := by sorry

end InteractiveConsistency.Impossibility
