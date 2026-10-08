-- Prove2me | Theorems.Thm_GavrilSubtree_Chordal_inter_cliques_disjoint
-- name    : GavrilSubtree.Chordal.inter_cliques_disjoint
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T07:53:33.106885+00:00
-- url     : https://prove2.me/theorems/d35ca334-ee6a-47f6-8f53-bf55282cd0e0
-- title:
--   §2, p. 50 — the subtree intersections of two different cliques are disjoint
-- statement:
--   Let $G$ be a graph represented by a family of subtrees $(\bar v)_{v \in V}$ of a tree $T$. For two different cliques (maximal completely connected sets) $A_1 \neq A_2$ of $G$,
--   $$\Big(\bigcap_{v \in A_1} \bar v\Big) \cap \Big(\bigcap_{v \in A_2} \bar v\Big) = \varnothing.$$
--
--   Together with Lemma 1 this says that the sets $s_A = \bigcap_{v \in A} \bar v$, $A \in \mu(G)$, are nonempty and pairwise disjoint, so one can pick a distinct tree point for each clique; this is the first step of the proof of Theorem 2.
--
--   **Formalization Note** No finiteness of $V$ is assumed; the statement holds for arbitrary graphs.
-- source:
--   Gavril, The intersection graphs of subtrees in trees are exactly the chordal graphs, J. Combin. Theory Ser. B 16 (1974), p. 50, §2, the sentence after the proof of Lemma 1

import Mathlib
import Definitions.Def_GavrilSubtree_Chordal_Setting

namespace GavrilSubtree.Chordal

universe u

theorem inter_cliques_disjoint {V : Type u} {G : SimpleGraph V} {β : Type u}
    {T : SimpleGraph β} {F : V → Set β} (hF : IsSubtreeRep G T F) (A₁ A₂ : Cliques G)
    (hne : A₁ ≠ A₂) :
    (⋂ v ∈ A₁.1, F v) ∩ (⋂ v ∈ A₂.1, F v) = ∅ := by sorry

end GavrilSubtree.Chordal
