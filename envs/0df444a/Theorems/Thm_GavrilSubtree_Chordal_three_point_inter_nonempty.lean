-- Prove2me | Theorems.Thm_GavrilSubtree_Chordal_three_point_inter_nonempty
-- name    : GavrilSubtree.Chordal.three_point_inter_nonempty
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T07:51:22.666092+00:00
-- url     : https://prove2.me/theorems/f86948c2-9bf3-4368-8dbb-7cd056c783c2
-- title:
--   §2, proof of Lemma 1, p. 50 — subtrees each containing two of three points have a common point
-- statement:
--   Let $T$ be a tree, let $a_1, a_2, a_3$ be three vertices of $T$, and let $(t_i)_{i \in I}$ be any family of subtrees of $T$ (nonempty vertex sets inducing connected subgraphs) such that every $t_i$ contains at least two of the three points $a_1, a_2, a_3$. Then the subtrees have a common point:
--   $$\bigcap_{i \in I} t_i \neq \varnothing.$$
--
--   This is the remark with which Gavril opens the proof of Lemma 1: the three simple paths between the pairs of points meet, and each subtree contains the path between the two points it contains. It is the base of the Helly-type property of subtrees used in Lemma 1.
--
--   **Formalization Note** The paper takes a subset $\bar F$ of the (finite) representing family $F$; the Lean statement allows an arbitrary index type $I$, which is a stronger statement and still true. For empty $I$ the intersection is the whole tree, which is nonempty.
-- source:
--   Gavril, The intersection graphs of subtrees in trees are exactly the chordal graphs, J. Combin. Theory Ser. B 16 (1974), p. 50, §2, proof of Lemma 1 (first paragraph)

import Mathlib
import Definitions.Def_GavrilSubtree_Chordal_Setting

namespace GavrilSubtree.Chordal

universe u

theorem three_point_inter_nonempty {β : Type u} (T : SimpleGraph β) (hT : T.IsTree)
    {ι : Type*} (t : ι → Set β) (ht : ∀ i, (T.induce (t i)).Connected) (a₁ a₂ a₃ : β)
    (h : ∀ i, (a₁ ∈ t i ∧ a₂ ∈ t i) ∨ (a₁ ∈ t i ∧ a₃ ∈ t i) ∨ (a₂ ∈ t i ∧ a₃ ∈ t i)) :
    (⋂ i, t i).Nonempty := by sorry

end GavrilSubtree.Chordal
