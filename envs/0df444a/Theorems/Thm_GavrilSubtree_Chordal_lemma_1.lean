-- Prove2me | Theorems.Thm_GavrilSubtree_Chordal_lemma_1
-- name    : GavrilSubtree.Chordal.lemma_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T07:53:22.438725+00:00
-- url     : https://prove2.me/theorems/ecceaffb-33ae-47ff-a9f0-c29131706766
-- title:
--   LEMMA 1, p. 50 — for every completely connected set A of a subtree graph, ⋂_{v∈A} v̄ ≠ ∅
-- statement:
--   Let $G$ be a graph represented by a family of subtrees $(\bar v)_{v \in V}$ of a tree $T$ (distinct vertices are adjacent exactly when their subtrees intersect). Then for every finite completely connected set $A$ of $G$ (a finite set of pairwise adjacent vertices)
--   $$\bigcap_{v \in A} \bar v \neq \varnothing.$$
--
--   This is the Helly property of subtrees of a tree: pairwise intersecting subtrees have a common point. It is what lets Theorem 2 attach to each clique a point of the tree.
--
--   **Formalization Note** The paper's graphs are finite, so every completely connected set is finite; the Lean statement takes $A$ as a `Finset` and does not assume $V$ finite. Finiteness of $A$ is necessary: infinitely many nested rays of an infinite tree pairwise intersect with empty intersection. For $A = \varnothing$ the intersection is the whole tree, which is nonempty.
-- source:
--   Gavril, The intersection graphs of subtrees in trees are exactly the chordal graphs, J. Combin. Theory Ser. B 16 (1974), p. 50, Lemma 1

import Mathlib
import Definitions.Def_GavrilSubtree_Chordal_Setting

namespace GavrilSubtree.Chordal

universe u

theorem lemma_1 {V : Type u} {G : SimpleGraph V} {β : Type u} {T : SimpleGraph β}
    {F : V → Set β} (hF : IsSubtreeRep G T F) (A : Finset V) (hA : G.IsClique (A : Set V)) :
    (⋂ v ∈ A, F v).Nonempty := by sorry

end GavrilSubtree.Chordal
