-- Prove2me | Theorems.Thm_MatchingPolytope_Multi_isClosed_poly
-- name    : MatchingPolytope.Multi.isClosed_poly
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T23:21:19.67508+00:00
-- url     : https://prove2.me/theorems/ecb162c5-c972-46b5-a109-6579477b44ce
-- title:
--   Multi: is Closed poly
-- statement:
--   The Multi construction uses the is Closed poly property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/edmonds-matching-polytope/blob/6198b8314ac88a5638120fcf15d5b58c024caaab/MatchingPolytope/Multigraph.lean#L327-L349
-- source:
--   https://github.com/jtraverso/edmonds-matching-polytope/blob/6198b8314ac88a5638120fcf15d5b58c024caaab/MatchingPolytope/Multigraph.lean#L327-L349

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

theorem MatchingPolytope.Multi.isClosed_poly (ends : E → Sym2 V) (W : Finset V) (F : Finset E) :
    IsClosed (Poly ends W F) := by sorry
