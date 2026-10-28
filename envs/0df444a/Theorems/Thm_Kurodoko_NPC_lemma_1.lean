-- Prove2me | Theorems.Thm_Kurodoko_NPC_lemma_1
-- name    : Kurodoko.NPC.lemma_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-24T09:35:31.733196+00:00
-- url     : https://prove2.me/theorems/2a8f57e1-dbdc-443d-b824-dc9ce91a0848
-- title:
--   Lemma 1, p. 698 — every ? square lies on a ray: walks in all four directions meet a ray end ! (corrected: Appendix A.1 tee_l orientation and literal keying)
-- statement:
--   **Lemma 1.** Every square containing a question mark lies on a ray.
--
--   Let $F$ be a formula whose clauses all have exactly three literals, and consider the board assembled from $F$ by the reduction, before the question marks receive values. For every square $v=(r,c)$ that holds a `?`, each of the four straight walks from $v$ meets a ray end `!` on the board: there are $k,k',k'',k'''\ge1$ with
--   $$(r,c-k),\quad (r,c+k'),\quad (r-k'',c),\quad (r+k''',c)$$
--   all on the board and all holding `!`.
--
--   This makes the values of the question marks (one plus the squares passed over before the first `!` in each direction) well defined, and it is what §4.4 uses to fix them.
--
--   Differences from the source:
--   - reading: "lies on a ray": a line from an end square, through squares white in all solutions, to a square black in all solutions → from every ? square of the assembled board a straight walk left, right, up and down meets a ! (a ray end of A.1) on the board; reason: §4.4 uses Lemma 1 only to find a certainly-black square in each direction; A.1 marks those squares with ! ("exclamation marks indicate where rays end") and fix_deferred_work walks to them
--   - correction: Appendix A.1 keys occurrences by the signed literal (count_vars, make_sorting_network) and sets tee_l = rotate(flip(ltee)) → occurrences keyed by the variable |v|; teeL = rotate ltee (teeR = flip teeL); reason: the printed program raises KeyError on every negated literal; with the printed tee_l the clause (x, x, x), which has no one-in-three assignment, yields a solvable 81 × 81 board (a counterexample to Theorem 4); §4.3 requires S (input south, outputs north and east)
--   - reading: "a SAT instance", the one-in-three-SAT of Ref. [5] → a CNF whose clauses all have exactly three literals (negations and repeated variables allowed); "exactly one true" counts literal occurrences; reason: §3 reduces from one-in-three-SAT of [5]; the routing of Appendix A.1 only lines up when every clause has three literals; the reduction has one wire per occurrence
-- source:
--   Kölker, Kurodoko is NP-Complete, J. Inf. Process. 20(3) (2012), p. 698 (PDF 5), §4.4, Lemma 1 and its proof; Appendix A.1, p. 700 (PDF 7) line 50 and pp. 701 (PDF 8) lines 217–233

import Mathlib
import Definitions.Def_CookPvsNP_defs
import Definitions.Def_ProjSchedTW_Complexity_Encoding
import Definitions.Def_Kurodoko_NPC_Puzzle
import Definitions.Def_Kurodoko_NPC_OneInThreeSat
import Definitions.Def_Kurodoko_NPC_Reduction

namespace Kurodoko.NPC

open CookPvsNP ProjSchedTW.Complexity

/-- Lemma 1, p. 698, in the form of §4.4 and `fix_deferred_work`: on the board assembled from a
formula whose clauses all have three literals, from every `?` square a straight walk to the
left, to the right, up and down meets a ray end `!` on the board. -/
theorem lemma_1 (F : CNF) (hF : ∀ C ∈ F, C.length = 3) (v : Cell)
    (hv : preBoard F v = GCell.qmark) :
    (∃ k, 1 ≤ k ∧ k ≤ v.2 ∧ preBoard F (v.1, v.2 - k) = GCell.bang) ∧
    (∃ k, 1 ≤ k ∧ preBoard F (v.1, v.2 + k) = GCell.bang) ∧
    (∃ k, 1 ≤ k ∧ k ≤ v.1 ∧ preBoard F (v.1 - k, v.2) = GCell.bang) ∧
    (∃ k, 1 ≤ k ∧ preBoard F (v.1 + k, v.2) = GCell.bang) := by sorry

end Kurodoko.NPC
