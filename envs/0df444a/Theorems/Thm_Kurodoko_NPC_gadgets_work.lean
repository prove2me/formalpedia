-- Prove2me | Theorems.Thm_Kurodoko_NPC_gadgets_work
-- name    : Kurodoko.NPC.gadgets_work
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-24T09:35:05.781998+00:00
-- url     : https://prove2.me/theorems/251641a6-de4e-47c4-925a-0ab4e132deb9
-- title:
--   §4.1, p. 696 — in every solution of a reduced instance every gadget obeys its relation (corrected: Appendix A.1 tee_l orientation and literal keying)
-- statement:
--   Let $F$ be a formula whose clauses all have exactly three literals, let $K(F)$ be the Kurodoko instance produced by the reduction, and let $B$ be a solution of $K(F)$. Then every gadget placed on the board satisfies its relation of §4.1 on the colours of its port squares (black $=1$, white $=0$):
--   1. Wire: $n_o=s_i$;
--   2. Negation: $n_o=1-s_i$;
--   3. Variable: no constraint;
--   4. Zero: $n_o=0$;
--   5. Xor, drawn as $X^2$: $s_o=w_i\oplus e_i$;
--   6. Choice: $w_i+s_i+e_i=1$;
--   7. Split: $w_o=e_o=s_i$;
--   8. Sidesplit, drawn as $S^+$: $e_o=s_o=w_i$;
--   9. Bend: $e_o=s_i$,
--
--   each read in the frame of the gadget's string and carried to the board through the rotations and mirrorings with which it is placed.
--
--   This is the claim of §4.1 ("we claim now—and prove later"), proved in §5 and Appendix A.2; Theorem 4 derives a one-in-three assignment from it.
--
--   Differences from the source:
--   - correction: Appendix A.1 keys occurrences by the signed literal (count_vars, make_sorting_network) and sets tee_l = rotate(flip(ltee)) → occurrences keyed by the variable |v|; teeL = rotate ltee (teeR = flip teeL); reason: the printed program raises KeyError on every negated literal; with the printed tee_l the clause (x, x, x), which has no one-in-three assignment, yields a solvable 81 × 81 board (a counterexample to Theorem 4); §4.3 requires S (input south, outputs north and east)
--   - reading: "a SAT instance", the one-in-three-SAT of Ref. [5] → a CNF whose clauses all have exactly three literals (negations and repeated variables allowed); "exactly one true" counts literal occurrences; reason: §3 reduces from one-in-three-SAT of [5]; the routing of Appendix A.1 only lines up when every clause has three literals; the reduction has one wire per occurrence
--   - encoding: the relations of §4.1 for the gadgets W, N, V, Z, X, C, T, S, B, rotated and mirrored as placed → GadgetRel on the colours of the port squares, stated in the frame of each A.1 string (the xor string is X², relation so = wi ⊕ ei; the ltee string is S+, relation eo = so = wi) and transported by the placement's rotate/flip operations; reason: rotating or mirroring a gadget moves its ports with it; the Xor and Sidesplit strings of A.1 draw X² and S+ (A.2.3, A.2.6)
--   - encoding: V = {0, …, w−1} × {0, …, h−1}, squares written (r, c) → squares (r, c) with row r < h and column c < w; reason: the paper indexes (r, c) with c < w in its definition of hz; the problem is symmetric under transposition
--   - reading: rule (3): the induced subgraph G_W on the white squares is connected → any two white squares are joined by a chain of adjacent white squares (the white set is preconnected); reason: the two differ only when there is no white square, i.e. on boards with at most one square; the paper's own checker (proof of Theorem 2) accepts w = h = 1 with no white square, and the empty boards (w = 0 or h = 0, no clues) it rejects are yes-instances here; NP-completeness is unaffected
--   - reading: rule (4): ∀(r, c) ∈ V : N(r, c) = hz + vt − 1, hz with the run {(r, b + i)}_{i=0}^{k} → for every clue (r, c, n): n = touchCount (the squares of its row and column reachable through white squares, itself once); reason: N is defined only on C, and a run of length k has the squares i = 0, …, k − 1; touchCount = hz + vt − 1 for a white clue square
-- source:
--   Kölker, Kurodoko is NP-Complete, J. Inf. Process. 20(3) (2012), p. 696 (PDF 3), §4.1, the list of gadget behaviours and "We claim now—and prove later …"; proved p. 698 (PDF 5), §5, and Appendix A.2, pp. 702–706 (PDF 9–13)

import Mathlib
import Definitions.Def_CookPvsNP_defs
import Definitions.Def_ProjSchedTW_Complexity_Encoding
import Definitions.Def_Kurodoko_NPC_Puzzle
import Definitions.Def_Kurodoko_NPC_OneInThreeSat
import Definitions.Def_Kurodoko_NPC_Reduction

namespace Kurodoko.NPC

open CookPvsNP ProjSchedTW.Complexity

/-- §4.1, p. 696 (proved in §5 and Appendix A.2): in every solution of the instance produced from
a formula whose clauses all have three literals, every placed gadget behaves as described, read
on the colours (black = true) of its port squares. -/
theorem gadgets_work (F : CNF) (hF : ∀ C ∈ F, C.length = 3) (B : Finset Cell)
    (hB : IsSolution (reduceCNF F).1 (reduceCNF F).2.1 (reduceCNF F).2.2 B) :
    ∀ p ∈ placements F, GadgetRel p.2.2.base (fun q => portCell p q ∈ B) := by sorry

end Kurodoko.NPC
