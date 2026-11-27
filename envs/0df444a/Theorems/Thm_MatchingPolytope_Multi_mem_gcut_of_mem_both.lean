-- Prove2me | Theorems.Thm_MatchingPolytope_Multi_mem_gcut_of_mem_both
-- name    : MatchingPolytope.Multi.mem_gcut_of_mem_both
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T23:25:05.912355+00:00
-- url     : https://prove2.me/theorems/1be21b64-47a1-5ffb-938d-f72902d5da90
-- title:
--   Multi: mem gcut of mem both
-- statement:
--   The Multi construction uses the mem gcut of mem both property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/edmonds-matching-polytope/blob/6198b8314ac88a5638120fcf15d5b58c024caaab/MatchingPolytope/Glue.lean#L157-L165
-- source:
--   https://github.com/jtraverso/edmonds-matching-polytope/blob/6198b8314ac88a5638120fcf15d5b58c024caaab/MatchingPolytope/Glue.lean#L157-L165

module
public import Definitions.Def_MatchingPolytope_Shrink
public import Definitions.Def_MatchingPolytope_Glue
set_option autoImplicit true
@[expose] public section
public section
open MatchingPolytope MatchingPolytope.Multi
open Finset
variable {V E : Type*}
variable {ends : E → Sym2 V} {W : Finset V} {F : Finset E}
variable [DecidableEq V]

theorem MatchingPolytope.Multi.mem_gcut_of_mem_both (hV : Valid ends W F) {S : Finset V} {e : E}
    (h1 : e ∈ shrinkF ends F S) (h2 : e ∈ shrinkF ends F (W \ S)) : e ∈ gcut ends F S := by sorry
