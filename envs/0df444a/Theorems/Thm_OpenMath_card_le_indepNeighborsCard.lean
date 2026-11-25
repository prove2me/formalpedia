-- Prove2me | Theorems.Thm_OpenMath_card_le_indepNeighborsCard
-- name    : OpenMath.card_le_indepNeighborsCard
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T19:37:03.495954+00:00
-- url     : https://prove2.me/theorems/dbedc063-f613-4e0d-b025-9b0d853a78cd
-- title:
--   Open Math: card le indep Neighbors Card
-- statement:
--   An independent set of neighbours of `u` has at most `l(u)` elements.
--
--   Source: https://github.com/v3ai/openmath/blob/a5525a12ad7c35c64ac14839f505ee2624016401/OpenMath/Common.lean#L119-L134
-- source:
--   https://github.com/v3ai/openmath/blob/a5525a12ad7c35c64ac14839f505ee2624016401/OpenMath/Common.lean#L119-L134

module
public import Mathlib.Combinatorics.SimpleGraph.Metric
public import Mathlib.Combinatorics.SimpleGraph.Diam
public import Mathlib.Combinatorics.SimpleGraph.Clique
public import Mathlib.Combinatorics.SimpleGraph.Bipartite
public import Mathlib.Data.Real.Basic
public import Definitions.Def_OpenMath_Common
set_option autoImplicit true
@[expose] public section
public section
set_option linter.unusedSectionVars false
open OpenMath
open SimpleGraph Finset
variable {α : Type*} [Fintype α] [DecidableEq α]

theorem OpenMath.card_le_indepNeighborsCard {G : SimpleGraph α} {u : α} {S : Finset α}
    (hS : ∀ x ∈ S, G.Adj u x) (hind : (S : Set α).Pairwise fun x y => ¬ G.Adj x y) :
    S.card ≤ indepNeighborsCard G u := by sorry
