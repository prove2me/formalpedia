-- Prove2me | Theorems.Thm_MatchingPolytope_Multi_mem_gcut_of_pair
-- name    : MatchingPolytope.Multi.mem_gcut_of_pair
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T23:18:57.632417+00:00
-- url     : https://prove2.me/theorems/573c3577-79ca-5e98-b509-f19b5530a713
-- title:
--   Multi: mem gcut of pair
-- statement:
--   The Multi construction uses the mem gcut of pair property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/edmonds-matching-polytope/blob/6198b8314ac88a5638120fcf15d5b58c024caaab/MatchingPolytope/Multigraph.lean#L79-L82
-- source:
--   https://github.com/jtraverso/edmonds-matching-polytope/blob/6198b8314ac88a5638120fcf15d5b58c024caaab/MatchingPolytope/Multigraph.lean#L79-L82

module
public import Mathlib
public import Definitions.Def_MatchingPolytope_Multigraph
set_option autoImplicit true
@[expose] public section
public section
open MatchingPolytope MatchingPolytope.Multi
open Finset
variable {V E : Type*}

theorem MatchingPolytope.Multi.mem_gcut_of_pair {ends : E → Sym2 V} {F : Finset E} {S : Finset V} {e : E} {a b : V}
    (h : ends e = s(a, b)) :
    e ∈ gcut ends F S ↔ e ∈ F ∧ (a ∈ S ∨ b ∈ S) ∧ (a ∉ S ∨ b ∉ S) := by sorry
