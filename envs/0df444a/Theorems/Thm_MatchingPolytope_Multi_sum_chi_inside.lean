-- Prove2me | Theorems.Thm_MatchingPolytope_Multi_sum_chi_inside
-- name    : MatchingPolytope.Multi.sum_chi_inside
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T23:20:35.610289+00:00
-- url     : https://prove2.me/theorems/e5e2a09a-12d3-408e-af6c-866354f556dc
-- title:
--   Multi: sum chi inside
-- statement:
--   The Multi construction uses the sum chi inside property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/edmonds-matching-polytope/blob/6198b8314ac88a5638120fcf15d5b58c024caaab/MatchingPolytope/Multigraph.lean#L224-L234
-- source:
--   https://github.com/jtraverso/edmonds-matching-polytope/blob/6198b8314ac88a5638120fcf15d5b58c024caaab/MatchingPolytope/Multigraph.lean#L224-L234

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

theorem MatchingPolytope.Multi.sum_chi_inside {M D : Finset E} (hM : M ⊆ D) (S : Finset V) :
    ∑ e ∈ inside ends D S, chi M e = ((inside ends M S).card : ℝ) := by sorry
