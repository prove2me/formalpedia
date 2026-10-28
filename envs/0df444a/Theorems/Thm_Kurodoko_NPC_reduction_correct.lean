-- Prove2me | Theorems.Thm_Kurodoko_NPC_reduction_correct
-- name    : Kurodoko.NPC.reduction_correct
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-24T09:34:43.101528+00:00
-- url     : https://prove2.me/theorems/7196f014-413a-48df-8310-8d21be6242f2
-- title:
--   §3, p. 695 — the reduction from one-in-three SAT is polynomial-time and exact (corrected: Appendix A.1 tee_l orientation and literal keying)
-- statement:
--   The reduction of §4 and Appendix A.1, as a map $f$ from words over the SAT alphabet to words over the instance alphabet, is computable in polynomial time, and for every word $s$
--   $$s\in\mathsf{1in3SAT}\iff f(s)\in\mathsf{Kurodoko}.$$
--   On the code of a formula $F$ whose clauses all have three literals, $f$ outputs the code of the instance $K(F)$; every other word goes to the code of a fixed unsolvable instance.
--
--   This names the paper's own map, so it is stronger than the bare reducibility $\mathsf{1in3SAT}\le_p\mathsf{Kurodoko}$; together with the NP-hardness of one-in-three SAT it gives Theorem 3.
--
--   **Formalization Note** Polynomial time is the published `CookPvsNP.PolyTimeComputable` (one-tape Turing machines). Membership of $f(s)$ in the Kurodoko language includes well-formedness of $K(F)$, in particular that every clue value lies in $\{1,\dots,w+h-1\}$.
--
--   Differences from the source:
--   - correction: Appendix A.1 keys occurrences by the signed literal (count_vars, make_sorting_network) and sets tee_l = rotate(flip(ltee)) → occurrences keyed by the variable |v|; teeL = rotate ltee (teeR = flip teeL); reason: the printed program raises KeyError on every negated literal; with the printed tee_l the clause (x, x, x), which has no one-in-three assignment, yields a solvable 81 × 81 board (a counterexample to Theorem 4); §4.3 requires S (input south, outputs north and east)
--   - reading: "a SAT instance", the one-in-three-SAT of Ref. [5] → a CNF whose clauses all have exactly three literals (negations and repeated variables allowed); "exactly one true" counts literal occurrences; reason: §3 reduces from one-in-three-SAT of [5]; the routing of Appendix A.1 only lines up when every clause has three literals; the reduction has one wire per occurrence
--   - encoding: the program fails on the empty formula (max of an empty dict) → reduceCNF [] = (1, 1, []), a solvable instance; reason: the empty formula is a yes-instance; no nonempty formula is affected
--   - encoding: the reduction is defined on SAT instances → reduceWord sends a word that is not the code of a 3-literal-clause formula to the code of the unsolvable instance w = 2, h = 1, clues (0,0,1), (0,1,1); reason: a many-one reduction on words must send non-instances to a no-instance; changes no instance
--   - encoding: w and h in binary, C as a list of points and N as a list of integers (p. 694) → code = encNats [w, h, r₁, c₁, n₁, r₂, c₂, n₂, …] (binary, clue triples interleaved), over the alphabet BSym; reason: a polynomial-time-equivalent layout of the same data; w and h stay binary
--   - encoding: V = {0, …, w−1} × {0, …, h−1}, squares written (r, c) → squares (r, c) with row r < h and column c < w; reason: the paper indexes (r, c) with c < w in its definition of hz; the problem is symmetric under transposition
--   - reading: rule (3): the induced subgraph G_W on the white squares is connected → any two white squares are joined by a chain of adjacent white squares (the white set is preconnected); reason: the two differ only when there is no white square, i.e. on boards with at most one square; the paper's own checker (proof of Theorem 2) accepts w = h = 1 with no white square, and the empty boards (w = 0 or h = 0, no clues) it rejects are yes-instances here; NP-completeness is unaffected
--   - reading: rule (4): ∀(r, c) ∈ V : N(r, c) = hz + vt − 1, hz with the run {(r, b + i)}_{i=0}^{k} → for every clue (r, c, n): n = touchCount (the squares of its row and column reachable through white squares, itself once); reason: N is defined only on C, and a run of length k has the squares i = 0, …, k − 1; touchCount = hz + vt − 1 for a white clue square
-- source:
--   Kölker, Kurodoko is NP-Complete, J. Inf. Process. 20(3) (2012), p. 695 (PDF 2), §3: "by showing how to compute a reduction from one-in-three-SAT"; §4, pp. 695–698 (PDF 2–5); Appendix A.1, pp. 700–702 (PDF 7–9)

import Mathlib
import Definitions.Def_CookPvsNP_defs
import Definitions.Def_ProjSchedTW_Complexity_Encoding
import Definitions.Def_Kurodoko_NPC_Puzzle
import Definitions.Def_Kurodoko_NPC_OneInThreeSat
import Definitions.Def_Kurodoko_NPC_Reduction

namespace Kurodoko.NPC

open CookPvsNP ProjSchedTW.Complexity

/-- §3, p. 695, with §4 and Appendix A.1: the reduction is computable in polynomial time and maps
one-in-three SAT exactly into the Kurodoko language. -/
theorem reduction_correct :
    PolyTimeComputable reduceWord ∧
      ∀ s, s ∈ oneInThreeLang ↔ reduceWord s ∈ kurodokoLang := by sorry

end Kurodoko.NPC
