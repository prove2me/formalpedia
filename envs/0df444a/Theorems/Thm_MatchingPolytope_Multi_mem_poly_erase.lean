-- Prove2me | Theorems.Thm_MatchingPolytope_Multi_mem_poly_erase
-- name    : MatchingPolytope.Multi.mem_poly_erase
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T23:26:20.835128+00:00
-- url     : https://prove2.me/theorems/ad0b9820-a9a3-4988-ab4b-9aac5f22903b
-- title:
--   Multi: mem poly erase
-- statement:
--   The Multi construction uses the mem poly erase property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/edmonds-matching-polytope/blob/6198b8314ac88a5638120fcf15d5b58c024caaab/MatchingPolytope/Induction.lean#L61-L69
-- source:
--   https://github.com/jtraverso/edmonds-matching-polytope/blob/6198b8314ac88a5638120fcf15d5b58c024caaab/MatchingPolytope/Induction.lean#L61-L69

module
public import Definitions.Def_MatchingPolytope_Glue
public import Definitions.Def_MatchingPolytope_Induction
set_option autoImplicit true
@[expose] public section
public section
open MatchingPolytope MatchingPolytope.Multi
open Finset
variable {V E : Type*} {ends : E → Sym2 V} {W : Finset V} {F : Finset E}

theorem MatchingPolytope.Multi.mem_poly_erase [DecidableEq E] {y : E → ℝ} (hy : y ∈ Poly ends W F) {e : E} (he0 : y e = 0) :
    y ∈ Poly ends W (F.erase e) := by sorry
