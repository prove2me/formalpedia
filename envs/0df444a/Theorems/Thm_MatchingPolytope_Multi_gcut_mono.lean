-- Prove2me | Theorems.Thm_MatchingPolytope_Multi_gcut_mono
-- name    : MatchingPolytope.Multi.gcut_mono
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T23:19:40.235795+00:00
-- url     : https://prove2.me/theorems/10ebeed1-0e27-5000-9676-7730b83740f3
-- title:
--   Multi: gcut mono
-- statement:
--   The Multi construction uses the gcut mono property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/edmonds-matching-polytope/blob/6198b8314ac88a5638120fcf15d5b58c024caaab/MatchingPolytope/Multigraph.lean#L137-L138
-- source:
--   https://github.com/jtraverso/edmonds-matching-polytope/blob/6198b8314ac88a5638120fcf15d5b58c024caaab/MatchingPolytope/Multigraph.lean#L137-L138

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

theorem MatchingPolytope.Multi.gcut_mono {D D' : Finset E} (h : D ⊆ D') (S : Finset V) : gcut ends D S ⊆ gcut ends D' S := by sorry
