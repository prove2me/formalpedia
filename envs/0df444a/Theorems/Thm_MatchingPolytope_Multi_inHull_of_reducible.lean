-- Prove2me | Theorems.Thm_MatchingPolytope_Multi_inHull_of_reducible
-- name    : MatchingPolytope.Multi.inHull_of_reducible
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T23:26:24.177121+00:00
-- url     : https://prove2.me/theorems/5ebcf5e9-f2e0-5389-b28c-207c7110a63c
-- title:
--   Multi: in Hull of reducible
-- statement:
--   Reducible points are in the hull, assuming the theorem for smaller multigraphs.
--
--   Source: https://github.com/jtraverso/edmonds-matching-polytope/blob/6198b8314ac88a5638120fcf15d5b58c024caaab/MatchingPolytope/Induction.lean#L72-L107
-- source:
--   https://github.com/jtraverso/edmonds-matching-polytope/blob/6198b8314ac88a5638120fcf15d5b58c024caaab/MatchingPolytope/Induction.lean#L72-L107

module
public import Definitions.Def_MatchingPolytope_Glue
public import Definitions.Def_MatchingPolytope_Induction
set_option autoImplicit true
@[expose] public section
public section
open MatchingPolytope MatchingPolytope.Multi
open Finset
variable {V E : Type*} {ends : E → Sym2 V} {W : Finset V} {F : Finset E}

theorem MatchingPolytope.Multi.inHull_of_reducible [DecidableEq V] [Fintype E]
    (IH : ∀ (ends' : E → Sym2 V) (W' : Finset V) (F' : Finset E),
      W'.card + F'.card < W.card + F.card → Valid ends' W' F' →
        ∀ x ∈ Poly ends' W' F', InHull (IsPM ends' W' F') x)
    (hV : Valid ends W F) {y : E → ℝ} (hy : y ∈ Poly ends W F) (hr : Reducible ends W F y) :
    InHull (IsPM ends W F) y := by sorry
