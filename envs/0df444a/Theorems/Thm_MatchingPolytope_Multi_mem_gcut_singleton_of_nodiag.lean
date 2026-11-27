-- Prove2me | Theorems.Thm_MatchingPolytope_Multi_mem_gcut_singleton_of_nodiag
-- name    : MatchingPolytope.Multi.mem_gcut_singleton_of_nodiag
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T23:19:06.992524+00:00
-- url     : https://prove2.me/theorems/92d10dbd-8b97-4f94-8892-83a7e13a396b
-- title:
--   Multi: mem gcut singleton of nodiag
-- statement:
--   The Multi construction uses the mem gcut singleton of nodiag property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/edmonds-matching-polytope/blob/6198b8314ac88a5638120fcf15d5b58c024caaab/MatchingPolytope/Multigraph.lean#L109-L125
-- source:
--   https://github.com/jtraverso/edmonds-matching-polytope/blob/6198b8314ac88a5638120fcf15d5b58c024caaab/MatchingPolytope/Multigraph.lean#L109-L125

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

theorem MatchingPolytope.Multi.mem_gcut_singleton_of_nodiag {D : Finset E} (hD : ∀ e ∈ D, ¬ (ends e).IsDiag) {e : E}
    {v : V} : e ∈ gcut ends D {v} ↔ e ∈ D ∧ v ∈ ends e := by sorry
