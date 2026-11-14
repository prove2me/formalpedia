-- Prove2me | Theorems.Thm_Mazoit2013_partial_decomposition_gluing
-- name    : Mazoit2013.partial_decomposition_gluing
-- status  : Proved
-- author  : @lreyzin
-- created : 2026-11-13T23:15:37.896232+00:00
-- url     : https://prove2.me/theorems/5a120bd5-57bc-4844-914e-443d6f53a726
-- title:
--   Gluing partial decompositions at non-touching flaps
-- statement:
--   Let two finite partial tree decompositions of a graph G have the same small-bag threshold b, with flap families dX and dY. Choose X in dX and Y in dY that do not touch. There exists another partial decomposition at threshold b such that each of its flaps is contained either in a member of dX other than X, or in a member of dY other than Y. The exclusions apply separately to the two input families. This is the remaining graph-specific gluing lemma; no large-treewidth hypothesis is needed.
-- source:
--   Mazoit, A simple proof of the tree-width duality theorem, https://arxiv.org/pdf/1309.2266, p. 2: partial and star decompositions, Lemma 1.

import Definitions.Def_Mazoit2013_PartialDecompositions
open RobertsonSeymour1986.GM5 StableMSR.Recovery.Havens StableMSR.Recovery.PartialDecompositions

theorem Mazoit2013.partial_decomposition_gluing {V : Type} [Fintype V] [DecidableEq V]
 (G : SimpleGraph V) (b : ℕ) (dX dY : Finset (Finset V))
 (hX : RealizableFlaps G b dX) (hY : RealizableFlaps G b dY)
 (X Y : Finset V) (hXX : X ∈ dX) (hYY : Y ∈ dY) (hnot : ¬ Touch G X Y) :
 ∃ d, RealizableFlaps G b d ∧ ∀ Z ∈ d,
 (∃ A ∈ dX, A ≠ X ∧ Z ⊆ A) ∨ (∃ A ∈ dY, A ≠ Y ∧ Z ⊆ A) := by sorry
