-- Prove2me | Theorems.Thm_MatchingPolytope_Multi_sum_degree
-- name    : MatchingPolytope.Multi.sum_degree
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T23:19:08.725083+00:00
-- url     : https://prove2.me/theorems/cc83a786-5d0e-4831-92d8-ed48907344e6
-- title:
--   Multi: sum degree
-- statement:
--   Double counting: summing degrees over `S` counts cut edges once and inner edges twice.
--
--   Source: https://github.com/jtraverso/edmonds-matching-polytope/blob/6198b8314ac88a5638120fcf15d5b58c024caaab/MatchingPolytope/Multigraph.lean#L176-L202
-- source:
--   https://github.com/jtraverso/edmonds-matching-polytope/blob/6198b8314ac88a5638120fcf15d5b58c024caaab/MatchingPolytope/Multigraph.lean#L176-L202

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

theorem MatchingPolytope.Multi.sum_degree {β : Type*} [AddCommMonoid β] (hV : Valid ends W F) {D : Finset E}
    (hD : D ⊆ F) (S : Finset V) (x : E → β) :
    ∑ v ∈ S, ∑ e ∈ gcut ends D {v}, x e =
      ∑ e ∈ gcut ends D S, x e + 2 • ∑ e ∈ inside ends D S, x e := by sorry
