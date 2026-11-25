-- Prove2me | Theorems.Thm_OpenMath_WOWII19_card_le_b_of_layered
-- name    : OpenMath.WOWII19.card_le_b_of_layered
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T19:38:26.965269+00:00
-- url     : https://prove2.me/theorems/bbb0f122-aed7-43c1-85f5-5dfbabcbf2c8
-- title:
--   WOWII19: card le b of layered
-- statement:
--   A vertex set in which adjacent vertices are never at the same distance from `v` induces a
--   bipartite subgraph.
--
--   Source: https://github.com/v3ai/openmath/blob/a5525a12ad7c35c64ac14839f505ee2624016401/OpenMath/WOWII19.lean#L86-L113
-- source:
--   https://github.com/v3ai/openmath/blob/a5525a12ad7c35c64ac14839f505ee2624016401/OpenMath/WOWII19.lean#L86-L113

module
public import Definitions.Def_OpenMath_Common
public import Mathlib.Algebra.Order.Floor.Ring
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring
public import Definitions.Def_OpenMath_WOWII19
set_option autoImplicit true
@[expose] public section
public section
set_option linter.unusedSectionVars false
open OpenMath OpenMath.WOWII19
open SimpleGraph Finset OpenMath
variable {α : Type*} [Fintype α] [DecidableEq α]

theorem OpenMath.WOWII19.card_le_b_of_layered {G : SimpleGraph α} (v : α) (H : Finset α)
    (hH : ∀ x ∈ H, ∀ y ∈ H, G.Adj x y → G.dist v x ≠ G.dist v y) :
    H.card ≤ largestInducedBipartiteSubgraphSize G := by sorry
