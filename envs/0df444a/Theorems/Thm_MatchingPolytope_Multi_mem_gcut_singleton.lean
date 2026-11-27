-- Prove2me | Theorems.Thm_MatchingPolytope_Multi_mem_gcut_singleton
-- name    : MatchingPolytope.Multi.mem_gcut_singleton
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T23:19:00.665245+00:00
-- url     : https://prove2.me/theorems/efb204b3-9bd4-5671-b919-cfd58f762ad8
-- title:
--   Multi: mem gcut singleton
-- statement:
--   The Multi construction uses the mem gcut singleton property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/edmonds-matching-polytope/blob/6198b8314ac88a5638120fcf15d5b58c024caaab/MatchingPolytope/Multigraph.lean#L127-L129
-- source:
--   https://github.com/jtraverso/edmonds-matching-polytope/blob/6198b8314ac88a5638120fcf15d5b58c024caaab/MatchingPolytope/Multigraph.lean#L127-L129

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

theorem MatchingPolytope.Multi.mem_gcut_singleton (hV : Valid ends W F) {D : Finset E} (hD : D ⊆ F) {e : E} {v : V} :
    e ∈ gcut ends D {v} ↔ e ∈ D ∧ v ∈ ends e := by sorry
