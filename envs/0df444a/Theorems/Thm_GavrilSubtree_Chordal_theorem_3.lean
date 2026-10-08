-- Prove2me | Theorems.Thm_GavrilSubtree_Chordal_theorem_3
-- name    : GavrilSubtree.Chordal.theorem_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T07:55:48.776492+00:00
-- url     : https://prove2.me/theorems/18a5708f-cd7a-4552-a25e-ce6d7ed68a45
-- title:
--   THEOREM 3, p. 51 — a finite graph is a subtree graph if and only if it is chordal
-- statement:
--   Let $G$ be a finite simple graph. Then $G$ is the intersection graph of a family of subtrees of a tree if and only if $G$ is chordal, i.e. every simple circuit of $G$ with more than three vertices has an edge connecting two non-consecutive vertices of the circuit:
--   $$G \text{ is a subtree graph} \iff G \text{ is chordal}.$$
--
--   This is the main theorem of Gavril's paper. It characterizes chordal graphs geometrically, generalizing interval graphs (intersection graphs of intervals of a line, the subtree graphs of a path), and underlies the clique-tree representation used for chordal graphs in sparse matrix elimination, database theory and graphical models.
--
--   **Formalization Note** Trees are combinatorial trees and subtrees are nonempty vertex sets inducing connected subgraphs (see the definitions file; this gives the same class of graphs as the paper's topological subtrees). Chordality is the cycle–chord definition, not a perfect-elimination ordering. $V$ is finite, as in the paper, and may be empty.
-- source:
--   Gavril, The intersection graphs of subtrees in trees are exactly the chordal graphs, J. Combin. Theory Ser. B 16 (1974), p. 51, Theorem 3

import Mathlib
import Definitions.Def_GavrilSubtree_Chordal_Setting

namespace GavrilSubtree.Chordal

universe u

theorem theorem_3 {V : Type u} [Fintype V] (G : SimpleGraph V) :
    IsSubtreeGraph G ↔ IsChordal G := by sorry

end GavrilSubtree.Chordal
