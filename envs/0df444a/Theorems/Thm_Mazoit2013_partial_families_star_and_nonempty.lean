-- Prove2me | Theorems.Thm_Mazoit2013_partial_families_star_and_nonempty
-- name    : Mazoit2013.partial_families_star_and_nonempty
-- status  : Proved
-- author  : @lreyzin
-- created : 2026-11-13T23:15:31.540102+00:00
-- url     : https://prove2.me/theorems/9c8ed188-fd42-4c4e-8fc4-c436586dd84b
-- title:
--   Nonempty partial-decomposition families and explicit star witnesses
-- statement:
--   Let G be a finite graph with no tree decomposition of width at most w. Every flap family realized by a partial decomposition at bag threshold w+1 is nonempty. Moreover, for every vertex set S of size at most w+1, one such realized family consists entirely of connected sets disjoint from S. The witnesses come from the star decomposition with central bag S and leaf bags S union C, one for each component C of G minus S. This discharges the nonemptiness and star-witness requirements in the bramble-extraction construction.
-- source:
--   Mazoit, A simple proof of the tree-width duality theorem, https://arxiv.org/pdf/1309.2266, p. 2: partial and star decompositions, Lemma 1.

import Definitions.Def_Mazoit2013_PartialDecompositions
open RobertsonSeymour1986.GM5 StableMSR.Recovery.Havens StableMSR.Recovery.PartialDecompositions

theorem Mazoit2013.partial_families_star_and_nonempty {V : Type} [Fintype V] [DecidableEq V]
 (G : SimpleGraph V) (w : ℕ) (hwidth : ¬ TreewidthLE G w) :
 (∀ d ∈ partialFamilies G (w+1), d.Nonempty) ∧
 (∀ S : Finset V, S.card < w+2 → ∃ d ∈ partialFamilies G (w+1),
   ∀ C ∈ d, ConnectedSet G C ∧ Disjoint S C) := by sorry
