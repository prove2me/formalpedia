-- Prove2me | Theorems.Thm_MatchingPolytope_Multi_inside_self
-- name    : MatchingPolytope.Multi.inside_self
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T23:20:40.726663+00:00
-- url     : https://prove2.me/theorems/f68ae6c9-1a05-4e39-bf44-c24f952c20bf
-- title:
--   Multi: inside self
-- statement:
--   The Multi construction uses the inside self property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/edmonds-matching-polytope/blob/6198b8314ac88a5638120fcf15d5b58c024caaab/MatchingPolytope/Multigraph.lean#L166-L173
-- source:
--   https://github.com/jtraverso/edmonds-matching-polytope/blob/6198b8314ac88a5638120fcf15d5b58c024caaab/MatchingPolytope/Multigraph.lean#L166-L173

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

theorem MatchingPolytope.Multi.inside_self (hV : Valid ends W F) {D : Finset E} (hD : D ⊆ F) : inside ends D W = D := by sorry
