-- Prove2me | Theorems.Thm_MatchingPolytope_Multi_card_shrinkW_lt
-- name    : MatchingPolytope.Multi.card_shrinkW_lt
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T23:22:20.876402+00:00
-- url     : https://prove2.me/theorems/0636b56f-ddeb-512e-9f7c-973610b7641f
-- title:
--   Multi: card shrink W lt
-- statement:
--   The Multi construction uses the card shrink W lt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/edmonds-matching-polytope/blob/6198b8314ac88a5638120fcf15d5b58c024caaab/MatchingPolytope/Shrink.lean#L94-L100
-- source:
--   https://github.com/jtraverso/edmonds-matching-polytope/blob/6198b8314ac88a5638120fcf15d5b58c024caaab/MatchingPolytope/Shrink.lean#L94-L100

module
public import Definitions.Def_MatchingPolytope_Multigraph
public import Definitions.Def_MatchingPolytope_Shrink
set_option autoImplicit true
@[expose] public section
public section
open MatchingPolytope MatchingPolytope.Multi
open Finset
variable {V E : Type*}
variable [DecidableEq V]
variable {ends : E → Sym2 V} {W : Finset V} {F : Finset E}

theorem MatchingPolytope.Multi.card_shrinkW_lt {R : Finset V} (hRW : R ⊆ W) (hR : 1 < R.card) (r : V) :
    (shrinkW W R r).card < W.card := by sorry
