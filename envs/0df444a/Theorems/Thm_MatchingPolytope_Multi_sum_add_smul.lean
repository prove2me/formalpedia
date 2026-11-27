-- Prove2me | Theorems.Thm_MatchingPolytope_Multi_sum_add_smul
-- name    : MatchingPolytope.Multi.sum_add_smul
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T23:26:47.313378+00:00
-- url     : https://prove2.me/theorems/99350100-1486-478e-b4e0-5af2921cb5da
-- title:
--   Multi: sum add smul
-- statement:
--   The Multi construction uses the sum add smul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/edmonds-matching-polytope/blob/6198b8314ac88a5638120fcf15d5b58c024caaab/MatchingPolytope/Induction.lean#L113-L115
-- source:
--   https://github.com/jtraverso/edmonds-matching-polytope/blob/6198b8314ac88a5638120fcf15d5b58c024caaab/MatchingPolytope/Induction.lean#L113-L115

module
public import Definitions.Def_MatchingPolytope_Glue
public import Definitions.Def_MatchingPolytope_Induction
set_option autoImplicit true
@[expose] public section
public section
open MatchingPolytope MatchingPolytope.Multi
open Finset
variable {V E : Type*} {ends : E → Sym2 V} {W : Finset V} {F : Finset E}

theorem MatchingPolytope.Multi.sum_add_smul (s : Finset E) (y d : E → ℝ) (ε : ℝ) :
    ∑ e ∈ s, (y + ε • d) e = ∑ e ∈ s, y e + ε * ∑ e ∈ s, d e := by sorry
