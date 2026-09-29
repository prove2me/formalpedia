-- Prove2me | Theorems.Thm_LocalSearchFL_UFL_exists_refined_pi
-- name    : LocalSearchFL.UFL.exists_refined_pi
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-26T18:15:55.972547+00:00
-- url     : https://prove2.me/theorems/b3122c22-6ee8-46a4-b89d-800c76daa00d
-- title:
--   Proof of Lemma 4.2, p. 555 — existence of the refined mapping π on each $N_O(o)$
-- statement:
--   Let $\sigma_S, \sigma_O : C \to F$ be any two assignments of the clients to facilities, with $N_S(s) = \sigma_S^{-1}(s)$, $N_O(o) = \sigma_O^{-1}(o)$ and $N^o_s = N_O(o) \cap N_S(s)$. Then there is a permutation $\pi$ of $C$ such that
--
--   1. $\pi$ maps every $N_O(o)$ onto itself;
--   2. (Property 3.1) whenever $|N^o_s| \le \tfrac12 |N_O(o)|$, $\pi(N^o_s) \cap N^o_s = \emptyset$;
--   3. whenever $|N^o_s| > \tfrac12 |N_O(o)|$, every $j \in N^o_s$ with $\pi(j) \in N^o_s$ satisfies $\pi(j) = j$.
--
--   This is the mapping on which the facility cost bound of Lemma 4.2 is built: a client whose serving facility in $S$ is closed is reassigned through $\pi$, and the fixed points of $\pi$ are exactly the clients of a captured block that cannot be moved to another block.
--
--   **Formalization Note** The family of bijections $\pi : N_O(o) \to N_O(o)$, one for each $o$, is encoded as a single permutation of all clients with $\sigma_O \circ \pi = \sigma_O$. The assignments are arbitrary maps: the statement is purely combinatorial.
-- source:
--   Arya, Garg, Khandekar, Meyerson, Munagala, Pandit, Local Search Heuristics for k-Median and Facility Location Problems, SIAM J. Comput. 33(3), 2004, p. 555, proof of Lemma 4.2, first paragraph (with Property 3.1 and its construction, p. 549)

import Mathlib
import Definitions.Def_LocalSearchFL_UFL_captures

namespace LocalSearchFL.UFL

/-- The mapping π of the proof of Lemma 4.2 (p. 555, first paragraph of the proof): for any
assignments `σS`, `σO` of the clients, there is a permutation `π` of the clients that maps each
`N_O(o)` onto itself, satisfies Property 3.1 (if `s` does not capture `o` then
`π(N^o_s) ∩ N^o_s = ∅`), and, when `s` captures `o`, fixes every `j ∈ N^o_s` with
`π(j) ∈ N^o_s`. -/
theorem exists_refined_pi {Cl Fa : Type} [Fintype Cl] [DecidableEq Cl] [DecidableEq Fa]
    (σS σO : Cl → Fa) :
    ∃ π : Equiv.Perm Cl, IsRefinedPi σS σO π := by sorry

end LocalSearchFL.UFL
