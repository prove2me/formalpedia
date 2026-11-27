-- Prove2me | Theorems.Thm_MatchingPolytope_Multi_gcut_subset
-- name    : MatchingPolytope.Multi.gcut_subset
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T23:19:04.010918+00:00
-- url     : https://prove2.me/theorems/8c5e26b8-e912-48c8-82e8-91657306c010
-- title:
--   Multi: gcut subset
-- statement:
--   The Multi construction uses the gcut subset property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/edmonds-matching-polytope/blob/6198b8314ac88a5638120fcf15d5b58c024caaab/MatchingPolytope/Multigraph.lean#L131-L132
-- source:
--   https://github.com/jtraverso/edmonds-matching-polytope/blob/6198b8314ac88a5638120fcf15d5b58c024caaab/MatchingPolytope/Multigraph.lean#L131-L132

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

theorem MatchingPolytope.Multi.gcut_subset (D : Finset E) (S : Finset V) : gcut ends D S ⊆ D := by sorry
