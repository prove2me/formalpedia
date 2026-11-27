-- Prove2me | Theorems.Thm_MatchingPolytope_Multi_InHull_of_mem
-- name    : MatchingPolytope.Multi.InHull.of_mem
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T23:20:47.424114+00:00
-- url     : https://prove2.me/theorems/37e59d68-fbf2-5847-91f4-103b358883c3
-- title:
--   In Hull: of mem
-- statement:
--   The In Hull construction uses the of mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/edmonds-matching-polytope/blob/6198b8314ac88a5638120fcf15d5b58c024caaab/MatchingPolytope/Multigraph.lean#L266-L273
-- source:
--   https://github.com/jtraverso/edmonds-matching-polytope/blob/6198b8314ac88a5638120fcf15d5b58c024caaab/MatchingPolytope/Multigraph.lean#L266-L273

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
variable [Fintype E]

theorem MatchingPolytope.Multi.InHull.of_mem {Q : Finset E → Prop} {M : Finset E} (hM : Q M) : InHull Q (chi M) := by sorry
