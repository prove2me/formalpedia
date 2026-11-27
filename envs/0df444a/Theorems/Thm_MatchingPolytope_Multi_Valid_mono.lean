-- Prove2me | Theorems.Thm_MatchingPolytope_Multi_Valid_mono
-- name    : MatchingPolytope.Multi.Valid.mono
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T23:19:32.759158+00:00
-- url     : https://prove2.me/theorems/a8a877fc-cdd1-51a2-9538-a9d66b85a1d1
-- title:
--   Valid: mono
-- statement:
--   The Valid construction uses the mono property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/edmonds-matching-polytope/blob/6198b8314ac88a5638120fcf15d5b58c024caaab/MatchingPolytope/Multigraph.lean#L98-L99
-- source:
--   https://github.com/jtraverso/edmonds-matching-polytope/blob/6198b8314ac88a5638120fcf15d5b58c024caaab/MatchingPolytope/Multigraph.lean#L98-L99

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

theorem MatchingPolytope.Multi.Valid.mono {F' : Finset E} (hV : Valid ends W F) (h : F' ⊆ F) : Valid ends W F' := by sorry
