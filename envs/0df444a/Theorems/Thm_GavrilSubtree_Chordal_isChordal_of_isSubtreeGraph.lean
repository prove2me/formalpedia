-- Prove2me | Theorems.Thm_GavrilSubtree_Chordal_isChordal_of_isSubtreeGraph
-- name    : GavrilSubtree.Chordal.isChordal_of_isSubtreeGraph
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T07:53:40.503155+00:00
-- url     : https://prove2.me/theorems/ecf15fb0-715c-4320-9e4c-bcb43128358e
-- title:
--   Proof of THEOREM 3 (first half), p. 51 — every subtree graph is chordal
-- statement:
--   Every subtree graph is chordal: if $G$ is the intersection graph of a family of subtrees of a tree, then every simple circuit of $G$ with more than three vertices has an edge joining two non-consecutive vertices of the circuit.
--   $$G \text{ is a subtree graph} \implies G \text{ is chordal}.$$
--
--   This is the "only if" half of the main theorem (Theorem 3). A chordless circuit of length at least four in $G$ would produce a circuit in the tree.
--
--   **Formalization Note** The vertex set $V$ is not assumed finite; the statement holds for arbitrary graphs, which is stronger than the paper's finite setting.
-- source:
--   Gavril, The intersection graphs of subtrees in trees are exactly the chordal graphs, J. Combin. Theory Ser. B 16 (1974), p. 51, §2, proof of Theorem 3, first paragraph

import Mathlib
import Definitions.Def_GavrilSubtree_Chordal_Setting

namespace GavrilSubtree.Chordal

universe u

theorem isChordal_of_isSubtreeGraph {V : Type u} (G : SimpleGraph V)
    (hG : IsSubtreeGraph G) : IsChordal G := by sorry

end GavrilSubtree.Chordal
