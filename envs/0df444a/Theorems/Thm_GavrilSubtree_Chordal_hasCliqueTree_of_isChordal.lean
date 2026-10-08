-- Prove2me | Theorems.Thm_GavrilSubtree_Chordal_hasCliqueTree_of_isChordal
-- name    : GavrilSubtree.Chordal.hasCliqueTree_of_isChordal
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T07:54:19.318879+00:00
-- url     : https://prove2.me/theorems/9bee74b7-82aa-436e-ada1-596fc73f9c28
-- title:
--   Proof of THEOREM 3 (second half), pp. 51–52 — every finite chordal graph has a clique tree
-- statement:
--   Let $G$ be a finite chordal graph. Then there is a tree $T$ whose vertex set is the set of cliques $\mu(G)$ such that, for every vertex $v$, the cliques containing $v$ induce a connected subtree $T(\mu_v(G))$:
--   $$G \text{ chordal} \implies \exists\, T \text{ tree on } \mu(G) \ \forall v \in V:\ T(\mu_v(G)) \text{ connected}.$$
--
--   Combined with Theorem 2 this gives the "if" half of the main theorem (Theorem 3).
--
--   **Formalization Note** $V$ is finite but may be empty.
-- source:
--   Gavril, The intersection graphs of subtrees in trees are exactly the chordal graphs, J. Combin. Theory Ser. B 16 (1974), pp. 51–52, §2, proof of Theorem 3, second and last paragraphs

import Mathlib
import Definitions.Def_GavrilSubtree_Chordal_Setting

namespace GavrilSubtree.Chordal

universe u

theorem hasCliqueTree_of_isChordal {V : Type u} [Fintype V] (G : SimpleGraph V)
    (hG : IsChordal G) : HasCliqueTree G := by sorry

end GavrilSubtree.Chordal
