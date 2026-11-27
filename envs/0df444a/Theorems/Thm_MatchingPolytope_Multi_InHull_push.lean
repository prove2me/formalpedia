-- Prove2me | Theorems.Thm_MatchingPolytope_Multi_InHull_push
-- name    : MatchingPolytope.Multi.InHull.push
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T23:20:56.946945+00:00
-- url     : https://prove2.me/theorems/b972896f-b9ad-476b-b94e-57dbe15c9563
-- title:
--   In Hull: push
-- statement:
--   Pushing forward a probability vector along a map to edge sets.
--
--   Source: https://github.com/jtraverso/edmonds-matching-polytope/blob/6198b8314ac88a5638120fcf15d5b58c024caaab/MatchingPolytope/Multigraph.lean#L297-L315
-- source:
--   https://github.com/jtraverso/edmonds-matching-polytope/blob/6198b8314ac88a5638120fcf15d5b58c024caaab/MatchingPolytope/Multigraph.lean#L297-L315

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

theorem MatchingPolytope.Multi.InHull.push {ι : Type*} [Fintype ι] {Q : Finset E → Prop} (c : ι → ℝ) (hc : ∀ i, 0 ≤ c i)
    (hc1 : ∑ i, c i = 1) (φ : ι → Finset E) (hφ : ∀ i, c i ≠ 0 → Q (φ i)) :
    InHull Q (∑ i, c i • chi (φ i)) := by sorry
