-- Prove2me | Theorems.Thm_MatchingPolytope_Multi_isPM_union
-- name    : MatchingPolytope.Multi.isPM_union
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T23:25:27.882978+00:00
-- url     : https://prove2.me/theorems/f4fa606c-dc15-48ea-9a94-92c69b3592fb
-- title:
--   Multi: is PM union
-- statement:
--   Gluing two matchings that agree on the cut of `S`.
--
--   Source: https://github.com/jtraverso/edmonds-matching-polytope/blob/6198b8314ac88a5638120fcf15d5b58c024caaab/MatchingPolytope/Glue.lean#L116-L155
-- source:
--   https://github.com/jtraverso/edmonds-matching-polytope/blob/6198b8314ac88a5638120fcf15d5b58c024caaab/MatchingPolytope/Glue.lean#L116-L155

module
public import Definitions.Def_MatchingPolytope_Shrink
public import Definitions.Def_MatchingPolytope_Glue
set_option autoImplicit true
@[expose] public section
public section
open MatchingPolytope MatchingPolytope.Multi
open Finset
variable {V E : Type*}
variable {ends : E → Sym2 V} {W : Finset V} {F : Finset E}
variable [DecidableEq V]

theorem MatchingPolytope.Multi.isPM_union [DecidableEq E] (hV : Valid ends W F) {S : Finset V} {M N : Finset E}
    (hM : M ⊆ shrinkF ends F S) (hN : N ⊆ shrinkF ends F (W \ S))
    (hcut : gcut ends M S = gcut ends N S)
    (hMdeg : ∀ v ∈ W, v ∉ S → (gcut ends M {v}).card = 1)
    (hNdeg : ∀ v ∈ W, v ∈ S → (gcut ends N {v}).card = 1) :
    IsPM ends W F (M ∪ N) := by sorry
