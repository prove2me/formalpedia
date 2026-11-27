-- Prove2me | Theorems.Thm_MatchingPolytope_Multi_exists_ker_of_card_lt
-- name    : MatchingPolytope.Multi.exists_ker_of_card_lt
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T23:26:50.771624+00:00
-- url     : https://prove2.me/theorems/5eb11d30-3f82-53b0-ada5-d44b1b40f40c
-- title:
--   Multi: exists ker of card lt
-- statement:
--   The Multi construction uses the exists ker of card lt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/edmonds-matching-polytope/blob/6198b8314ac88a5638120fcf15d5b58c024caaab/MatchingPolytope/Induction.lean#L220-L242
-- source:
--   https://github.com/jtraverso/edmonds-matching-polytope/blob/6198b8314ac88a5638120fcf15d5b58c024caaab/MatchingPolytope/Induction.lean#L220-L242

module
public import Definitions.Def_MatchingPolytope_Glue
public import Definitions.Def_MatchingPolytope_Induction
set_option autoImplicit true
@[expose] public section
public section
open MatchingPolytope MatchingPolytope.Multi
open Finset
variable {V E : Type*} {ends : E → Sym2 V} {W : Finset V} {F : Finset E}

theorem MatchingPolytope.Multi.exists_ker_of_card_lt [Finite E] (hlt : W.card < F.card) :
    ∃ d, Ker ends W F d ∧ d ≠ 0 := by sorry
