-- Prove2me | Theorems.Thm_MatchingPolytope_Multi_mem_shrinkF_or
-- name    : MatchingPolytope.Multi.mem_shrinkF_or
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T23:25:45.204691+00:00
-- url     : https://prove2.me/theorems/a4017d33-46dc-41fe-a318-34c463dd07d3
-- title:
--   Multi: mem shrink F or
-- statement:
--   The Multi construction uses the mem shrink F or property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/edmonds-matching-polytope/blob/6198b8314ac88a5638120fcf15d5b58c024caaab/MatchingPolytope/Glue.lean#L174-L179
-- source:
--   https://github.com/jtraverso/edmonds-matching-polytope/blob/6198b8314ac88a5638120fcf15d5b58c024caaab/MatchingPolytope/Glue.lean#L174-L179

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

theorem MatchingPolytope.Multi.mem_shrinkF_or (hV : Valid ends W F) {S : Finset V} {e : E} (he : e ∈ F) :
    e ∈ shrinkF ends F S ∨ e ∈ shrinkF ends F (W \ S) := by sorry
