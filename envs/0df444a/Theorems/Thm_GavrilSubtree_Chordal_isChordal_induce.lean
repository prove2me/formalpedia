-- Prove2me | Theorems.Thm_GavrilSubtree_Chordal_isChordal_induce
-- name    : GavrilSubtree.Chordal.isChordal_induce
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T07:54:25.917975+00:00
-- url     : https://prove2.me/theorems/2cd22142-e248-4410-9a52-6f0b8ab86c87
-- title:
--   Proof of THEOREM 3, p. 52 — induced subgraphs of a chordal graph are chordal
-- statement:
--   Let $G$ be a chordal graph on $V$ and $S \subseteq V$ any set of vertices. Then the induced subgraph $G(S)$ (vertex set $S$, two vertices adjacent iff they are adjacent in $G$) is chordal:
--   $$G \text{ chordal} \implies G(S) \text{ chordal}.$$
--
--   In the proof of Theorem 3 this is applied to $G_1 = G((V - A) \cup S)$, so that the induction hypothesis applies to $G_1$.
--
--   **Formalization Note** The paper asserts the claim for the particular subgraph $G((V-A)\cup S)$; the Lean statement covers every vertex subset of every (possibly infinite) graph, which is stronger.
-- source:
--   Gavril, The intersection graphs of subtrees in trees are exactly the chordal graphs, J. Combin. Theory Ser. B 16 (1974), p. 52, §2, proof of Theorem 3, second paragraph

import Mathlib
import Definitions.Def_GavrilSubtree_Chordal_Setting

namespace GavrilSubtree.Chordal

universe u

theorem isChordal_induce {V : Type u} (G : SimpleGraph V) (hG : IsChordal G) (s : Set V) :
    IsChordal (G.induce s) := by sorry

end GavrilSubtree.Chordal
