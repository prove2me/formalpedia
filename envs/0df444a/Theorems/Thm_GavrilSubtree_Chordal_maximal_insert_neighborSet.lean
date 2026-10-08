-- Prove2me | Theorems.Thm_GavrilSubtree_Chordal_maximal_insert_neighborSet
-- name    : GavrilSubtree.Chordal.maximal_insert_neighborSet
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T07:54:02.69148+00:00
-- url     : https://prove2.me/theorems/493edd9f-d8e4-40b8-9a26-cdfc54cd7134
-- title:
--   Proof of THEOREM 3, p. 52 — for a simplicial vertex v, {v} ∪ Γv is a clique
-- statement:
--   Let $v$ be a simplicial vertex of a graph $G$, i.e. its set of neighbours $\Gamma v$ is completely connected. Then
--   $$A = \{v\} \cup \Gamma v$$
--   is a clique of $G$, that is, a maximal completely connected set.
--
--   In the inductive step of the proof of Theorem 3 this clique $A$ is the one that is attached to the clique tree of a smaller chordal graph.
--
--   **Formalization Note** On p. 52 the paper writes $\tilde v$ for the chosen simplicial vertex (a vertex of $G$, not a subtree). The paper states the claim for chordal $G$; chordality is not needed and is not assumed, so the Lean statement is stronger.
-- source:
--   Gavril, The intersection graphs of subtrees in trees are exactly the chordal graphs, J. Combin. Theory Ser. B 16 (1974), p. 52, §2, proof of Theorem 3, second paragraph

import Mathlib
import Definitions.Def_GavrilSubtree_Chordal_Setting

namespace GavrilSubtree.Chordal

universe u

theorem maximal_insert_neighborSet {V : Type u} (G : SimpleGraph V) (v : V)
    (hv : IsSimplicial G v) : Maximal G.IsClique (insert v (G.neighborSet v)) := by sorry

end GavrilSubtree.Chordal
