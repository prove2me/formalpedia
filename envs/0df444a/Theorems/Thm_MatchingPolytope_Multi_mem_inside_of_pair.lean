-- Prove2me | Theorems.Thm_MatchingPolytope_Multi_mem_inside_of_pair
-- name    : MatchingPolytope.Multi.mem_inside_of_pair
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T23:19:06.256923+00:00
-- url     : https://prove2.me/theorems/c8b33ee5-70c0-4def-9583-78dc7c207053
-- title:
--   Multi: mem inside of pair
-- statement:
--   The Multi construction uses the mem inside of pair property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/edmonds-matching-polytope/blob/6198b8314ac88a5638120fcf15d5b58c024caaab/MatchingPolytope/Multigraph.lean#L84-L87
-- source:
--   https://github.com/jtraverso/edmonds-matching-polytope/blob/6198b8314ac88a5638120fcf15d5b58c024caaab/MatchingPolytope/Multigraph.lean#L84-L87

module
public import Mathlib
public import Definitions.Def_MatchingPolytope_Multigraph
set_option autoImplicit true
@[expose] public section
public section
open MatchingPolytope MatchingPolytope.Multi
open Finset
variable {V E : Type*}

theorem MatchingPolytope.Multi.mem_inside_of_pair {ends : E → Sym2 V} {F : Finset E} {S : Finset V} {e : E} {a b : V}
    (h : ends e = s(a, b)) :
    e ∈ inside ends F S ↔ e ∈ F ∧ a ∈ S ∧ b ∈ S := by sorry
