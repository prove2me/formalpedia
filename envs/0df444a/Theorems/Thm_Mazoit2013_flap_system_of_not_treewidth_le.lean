-- Prove2me | Theorems.Thm_Mazoit2013_flap_system_of_not_treewidth_le
-- name    : Mazoit2013.flap_system_of_not_treewidth_le
-- status  : Proved
-- author  : @lreyzin
-- created : 2026-11-13T23:02:00.723486+00:00
-- url     : https://prove2.me/theorems/b7d69b34-2191-4e6e-b978-c14e265d34b6
-- title:
--   Partial-decomposition flap system for a graph of large treewidth
-- statement:
--   Suppose a finite graph G has no tree decomposition of width at most w. There exist a finite family F of admissible vertex sets and a finite collection D of nonempty subfamilies of F with two properties. First, non-touching members X of dX and Y of dY can be eliminated by gluing: some family d in D has every member contained in a member of dX other than X or a member of dY other than Y. Second, every vertex set W of size at most w+1 has a family in D consisting entirely of nonempty connected sets disjoint from W. The intended witnesses are the flap families of partial decompositions with small-bag threshold w+1. This theorem supplies the graph-specific construction, gluing and star-family properties needed by the separately proved finite bramble-extraction argument. These properties remain to be formalized.
-- source:
--   Mazoit, A simple proof of the tree-width duality theorem, https://arxiv.org/pdf/1309.2266, p. 2: partial decompositions, star decompositions and Lemma 1; p. 3: nonempty flap families under large treewidth.

import Definitions.Def_SeymourThomas1993_Brambles
import Definitions.Def_RobertsonSeymour1986_GM5_TreewidthLE
set_option autoImplicit false
open StableMSR.Recovery.Brambles StableMSR.Recovery.Havens RobertsonSeymour1986.GM5

namespace Mazoit2013
theorem flap_system_of_not_treewidth_le {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (w : ℕ) (hwidth : ¬ TreewidthLE G w) :
    ∃ (F : Finset (Finset V)) (D : Finset (Finset (Finset V))),
      (∀ d ∈ D, d.Nonempty ∧ d ⊆ F) ∧
      (∀ dX ∈ D, ∀ dY ∈ D, ∀ X ∈ dX, ∀ Y ∈ dY, ¬ Touch G X Y →
        ∃ d ∈ D, ∀ Z ∈ d,
          (∃ A ∈ dX, A ≠ X ∧ Z ⊆ A) ∨ (∃ A ∈ dY, A ≠ Y ∧ Z ⊆ A)) ∧
      (∀ W : Finset V, W.card < w+2 →
        ∃ d ∈ D, ∀ X ∈ d, ConnectedSet G X ∧ Disjoint W X) := by sorry
end Mazoit2013
