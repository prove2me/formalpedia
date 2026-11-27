-- Prove2me | Theorems.Thm_MatchingPolytope_Multi_card_gcut_odd
-- name    : MatchingPolytope.Multi.card_gcut_odd
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T23:19:26.044249+00:00
-- url     : https://prove2.me/theorems/b70e6e48-bb98-5371-9269-79d1cb708dbf
-- title:
--   Multi: card gcut odd
-- statement:
--   The Multi construction uses the card gcut odd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/edmonds-matching-polytope/blob/6198b8314ac88a5638120fcf15d5b58c024caaab/MatchingPolytope/Multigraph.lean#L236-L248
-- source:
--   https://github.com/jtraverso/edmonds-matching-polytope/blob/6198b8314ac88a5638120fcf15d5b58c024caaab/MatchingPolytope/Multigraph.lean#L236-L248

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

theorem MatchingPolytope.Multi.card_gcut_odd (hV : Valid ends W F) {M : Finset E} (hM : IsPM ends W F M) {S : Finset V}
    (hS : S ⊆ W) (hodd : Odd S.card) : Odd (gcut ends M S).card := by sorry
