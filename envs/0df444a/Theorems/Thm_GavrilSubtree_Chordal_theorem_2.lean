-- Prove2me | Theorems.Thm_GavrilSubtree_Chordal_theorem_2
-- name    : GavrilSubtree.Chordal.theorem_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T07:53:46.065725+00:00
-- url     : https://prove2.me/theorems/0738060e-0be1-4481-ada6-197a896eb5cf
-- title:
--   THEOREM 2, p. 51 — G is a subtree graph iff there is a tree on μ(G) in which every μ_v(G) induces a connected subgraph
-- statement:
--   Let $G$ be a finite graph on vertex set $V$, with set of cliques $\mu(G)$ and, for $v \in V$, $\mu_v(G)$ the set of cliques containing $v$. Then
--   $$G \text{ is a subtree graph} \iff \exists \text{ a tree } T \text{ with vertex set } \mu(G) \text{ such that } T(\mu_v(G)) \text{ is connected for every } v \in V.$$
--
--   The right-hand side, a *clique tree*, is the canonical form of a subtree representation: the tree's vertices are the cliques and the subtree of $v$ is the set of cliques containing $v$. Theorem 2 reduces the main theorem to constructing a clique tree for every chordal graph.
--
--   **Formalization Note** $V$ is finite (the paper's standing assumption) but may be empty: then $\mu(G) = \{\varnothing\}$ and both sides hold. Connectedness of $T(\mu_v(G))$ includes nonemptiness, i.e. every vertex lies in a clique, which holds for finite graphs.
-- source:
--   Gavril, The intersection graphs of subtrees in trees are exactly the chordal graphs, J. Combin. Theory Ser. B 16 (1974), p. 51, Theorem 2

import Mathlib
import Definitions.Def_GavrilSubtree_Chordal_Setting

namespace GavrilSubtree.Chordal

universe u

theorem theorem_2 {V : Type u} [Fintype V] (G : SimpleGraph V) :
    IsSubtreeGraph G ↔ HasCliqueTree G := by sorry

end GavrilSubtree.Chordal
