-- Prove2me | Theorems.Thm_Mazoit2013_bramble_from_flap_families
-- name    : Mazoit2013.bramble_from_flap_families
-- status  : Proved
-- author  : @lreyzin
-- created : 2026-11-13T20:02:35.907501+00:00
-- url     : https://prove2.me/theorems/7bf41514-a789-4087-a349-0846154d16ad
-- title:
--   Bramble extraction from gluing and star-decomposition properties
-- statement:
--   Let F be a finite family of admissible vertex sets of a graph G, and let D be a finite collection of nonempty subfamilies of F. Assume the following gluing property: if X belongs to a family dX, Y belongs to dY, and X and Y do not touch, there is a family d in D every member of which is contained in some member of dX other than X or some member of dY other than Y. Also assume that for each vertex set W of size less than k, D contains a family all of whose members are connected, nonempty, and disjoint from W. Then F contains a bramble of order at least k. These are precisely the finite extremal and star-family steps of the partial-decomposition proof; the graph-specific construction and gluing of partial tree decompositions are explicit hypotheses, not asserted by this theorem.
-- source:
--   Mazoit, A simple proof of the tree-width duality theorem, https://arxiv.org/pdf/1309.2266, p. 3, forward implication, using Lemma 1 and star decompositions from p. 2.

import Definitions.Def_SeymourThomas1993_Brambles
set_option autoImplicit false
open StableMSR.Recovery.Brambles StableMSR.Recovery.Havens

namespace Mazoit2013
theorem bramble_from_flap_families {V : Type} [DecidableEq V]
    (G : SimpleGraph V) (F : Finset (Finset V)) (D : Finset (Finset (Finset V))) (k : ℕ)
    (hfamilies : ∀ d ∈ D, d.Nonempty ∧ d ⊆ F)
    (hglue : ∀ dX ∈ D, ∀ dY ∈ D, ∀ X ∈ dX, ∀ Y ∈ dY, ¬ Touch G X Y →
      ∃ d ∈ D, ∀ Z ∈ d,
        (∃ A ∈ dX, A ≠ X ∧ Z ⊆ A) ∨ (∃ A ∈ dY, A ≠ Y ∧ Z ⊆ A))
    (hstar : ∀ W : Finset V, W.card < k →
      ∃ d ∈ D, ∀ X ∈ d, ConnectedSet G X ∧ Disjoint W X) :
    ∃ B : Finset (Finset V), B ⊆ F ∧ IsBramble G B ∧ OrderAtLeast B k := by sorry
end Mazoit2013
