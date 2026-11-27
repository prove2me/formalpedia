-- Prove2me | Theorems.Thm_MatchingPolytope_Multi_odd_card_sdiff
-- name    : MatchingPolytope.Multi.odd_card_sdiff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T23:26:16.188546+00:00
-- url     : https://prove2.me/theorems/d9c51a9c-a551-5f41-b86b-781fcfbad9b4
-- title:
--   Multi: odd card sdiff
-- statement:
--   The Multi construction uses the odd card sdiff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/edmonds-matching-polytope/blob/6198b8314ac88a5638120fcf15d5b58c024caaab/MatchingPolytope/Induction.lean#L42-L48
-- source:
--   https://github.com/jtraverso/edmonds-matching-polytope/blob/6198b8314ac88a5638120fcf15d5b58c024caaab/MatchingPolytope/Induction.lean#L42-L48

module
public import Definitions.Def_MatchingPolytope_Glue
public import Definitions.Def_MatchingPolytope_Induction
set_option autoImplicit true
@[expose] public section
public section
open MatchingPolytope MatchingPolytope.Multi
open Finset
variable {V E : Type*} {ends : E → Sym2 V} {W : Finset V} {F : Finset E}

theorem MatchingPolytope.Multi.odd_card_sdiff [DecidableEq V] {S : Finset V} (hSW : S ⊆ W) (hW : Even W.card)
    (hS : Odd S.card) :
    Odd (W \ S).card := by sorry
