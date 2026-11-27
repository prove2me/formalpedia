-- Prove2me | Theorems.Thm_MatchingPolytope_Multi_sum_chi_gcut
-- name    : MatchingPolytope.Multi.sum_chi_gcut
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T23:19:28.219417+00:00
-- url     : https://prove2.me/theorems/f71e9bd1-6150-4d89-b77f-85c19bf573b7
-- title:
--   Multi: sum chi gcut
-- statement:
--   The Multi construction uses the sum chi gcut property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/edmonds-matching-polytope/blob/6198b8314ac88a5638120fcf15d5b58c024caaab/MatchingPolytope/Multigraph.lean#L212-L222
-- source:
--   https://github.com/jtraverso/edmonds-matching-polytope/blob/6198b8314ac88a5638120fcf15d5b58c024caaab/MatchingPolytope/Multigraph.lean#L212-L222

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

theorem MatchingPolytope.Multi.sum_chi_gcut {M D : Finset E} (hM : M ⊆ D) (S : Finset V) :
    ∑ e ∈ gcut ends D S, chi M e = ((gcut ends M S).card : ℝ) := by sorry
