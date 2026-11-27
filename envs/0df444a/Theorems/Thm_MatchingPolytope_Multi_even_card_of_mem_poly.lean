-- Prove2me | Theorems.Thm_MatchingPolytope_Multi_even_card_of_mem_poly
-- name    : MatchingPolytope.Multi.even_card_of_mem_poly
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T23:20:26.354919+00:00
-- url     : https://prove2.me/theorems/0ae2a6a7-8e97-5161-b2a8-c4c40a8582e8
-- title:
--   Multi: even card of mem poly
-- statement:
--   The Multi construction uses the even card of mem poly property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/edmonds-matching-polytope/blob/6198b8314ac88a5638120fcf15d5b58c024caaab/MatchingPolytope/Multigraph.lean#L204-L210
-- source:
--   https://github.com/jtraverso/edmonds-matching-polytope/blob/6198b8314ac88a5638120fcf15d5b58c024caaab/MatchingPolytope/Multigraph.lean#L204-L210

module
public import Mathlib
public import Definitions.Def_MatchingPolytope_Multigraph
set_option autoImplicit true
@[expose] public section
public section
open MatchingPolytope MatchingPolytope.Multi
open Finset
variable {V E : Type*}
variable {ends : E → Sym2 V} {W : Finset V} {F : Finset E}

theorem MatchingPolytope.Multi.even_card_of_mem_poly (hV : Valid ends W F) {x : E → ℝ} (hx : x ∈ Poly ends W F) :
    Even W.card := by sorry
