-- Prove2me | Theorems.Thm_Kurodoko_NPC_theorem_5
-- name    : Kurodoko.NPC.theorem_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-24T09:34:43.03898+00:00
-- url     : https://prove2.me/theorems/672ed80f-1769-4178-8308-3000a2c7d130
-- title:
--   Theorem 5, p. 699 — if the SAT instance has a solution, the reduced Kurodoko instance has one (corrected: Appendix A.1 tee_l orientation and literal keying)
-- statement:
--   **Theorem 5.** Let a SAT instance be given, and let $K$ be the Kurodoko instance produced by the reduction when run on the given SAT instance. If the SAT instance has a solution, then $K$ has a solution as well.
--
--   Here the SAT instance is a formula $F$ of one-in-three SAT, every clause with exactly three literals, and $K=K(F)$. The statement is
--   $$F\ \text{has a one-in-three assignment}\ \Longrightarrow\ K(F)\ \text{has a solution}.$$
--
--   This is the completeness half of the correctness of the reduction.
--
--   Differences from the source:
--   - reading: "a SAT instance", the one-in-three-SAT of Ref. [5] → a CNF whose clauses all have exactly three literals (negations and repeated variables allowed); "exactly one true" counts literal occurrences; reason: §3 reduces from one-in-three-SAT of [5]; the routing of Appendix A.1 only lines up when every clause has three literals; the reduction has one wire per occurrence
--   - correction: Appendix A.1 keys occurrences by the signed literal (count_vars, make_sorting_network) and sets tee_l = rotate(flip(ltee)) → occurrences keyed by the variable |v|; teeL = rotate ltee (teeR = flip teeL); reason: the printed program raises KeyError on every negated literal; with the printed tee_l the clause (x, x, x), which has no one-in-three assignment, yields a solvable 81 × 81 board (a counterexample to Theorem 4); §4.3 requires S (input south, outputs north and east)
--   - encoding: the program fails on the empty formula (max of an empty dict) → reduceCNF [] = (1, 1, []), a solvable instance; reason: the empty formula is a yes-instance; no nonempty formula is affected
--   - reading: rule (3): the induced subgraph G_W on the white squares is connected → any two white squares are joined by a chain of adjacent white squares (the white set is preconnected); reason: the two differ only when there is no white square, i.e. on boards with at most one square; the paper's own checker (proof of Theorem 2) accepts w = h = 1 with no white square, and the empty boards (w = 0 or h = 0, no clues) it rejects are yes-instances here; NP-completeness is unaffected
--   - reading: rule (4): ∀(r, c) ∈ V : N(r, c) = hz + vt − 1, hz with the run {(r, b + i)}_{i=0}^{k} → for every clue (r, c, n): n = touchCount (the squares of its row and column reachable through white squares, itself once); reason: N is defined only on C, and a run of length k has the squares i = 0, …, k − 1; touchCount = hz + vt − 1 for a white clue square
--   - encoding: V = {0, …, w−1} × {0, …, h−1}, squares written (r, c) → squares (r, c) with row r < h and column c < w; reason: the paper indexes (r, c) with c < w in its definition of hz; the problem is symmetric under transposition
-- source:
--   Kölker, Kurodoko is NP-Complete, J. Inf. Process. 20(3) (2012), p. 699 (PDF 6) – p. 700 (PDF 7), Theorem 5 and its proof

import Mathlib
import Definitions.Def_CookPvsNP_defs
import Definitions.Def_ProjSchedTW_Complexity_Encoding
import Definitions.Def_Kurodoko_NPC_Puzzle
import Definitions.Def_Kurodoko_NPC_OneInThreeSat
import Definitions.Def_Kurodoko_NPC_Reduction

namespace Kurodoko.NPC

open CookPvsNP ProjSchedTW.Complexity

/-- Theorem 5, p. 699: if a one-in-three SAT instance (every clause has three literals) has a
solution, then the Kurodoko instance produced from it has a solution. -/
theorem theorem_5 (F : CNF) (hF : ∀ C ∈ F, C.length = 3) (hS : OneInThree F) :
    Solvable (reduceCNF F).1 (reduceCNF F).2.1 (reduceCNF F).2.2 := by sorry

end Kurodoko.NPC
