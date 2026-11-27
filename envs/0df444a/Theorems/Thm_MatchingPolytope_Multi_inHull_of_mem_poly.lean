-- Prove2me | Theorems.Thm_MatchingPolytope_Multi_inHull_of_mem_poly
-- name    : MatchingPolytope.Multi.inHull_of_mem_poly
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T23:27:10.917555+00:00
-- url     : https://prove2.me/theorems/2ab7b4da-b192-548c-a940-fd8fbc160ddd
-- title:
--   Multi: in Hull of mem poly
-- statement:
--   **Edmonds' theorem for multigraphs**: every point of the polytope is a convex combination
--   of perfect matchings.
--
--   Source: https://github.com/jtraverso/edmonds-matching-polytope/blob/6198b8314ac88a5638120fcf15d5b58c024caaab/MatchingPolytope/Induction.lean#L470-L481
-- source:
--   https://github.com/jtraverso/edmonds-matching-polytope/blob/6198b8314ac88a5638120fcf15d5b58c024caaab/MatchingPolytope/Induction.lean#L470-L481

module
public import Definitions.Def_MatchingPolytope_Glue
public import Definitions.Def_MatchingPolytope_Induction
set_option autoImplicit true
@[expose] public section
public section
open MatchingPolytope MatchingPolytope.Multi
open Finset
variable {V E : Type*} {ends : E → Sym2 V} {W : Finset V} {F : Finset E}

theorem MatchingPolytope.Multi.inHull_of_mem_poly [Fintype E] (ends : E → Sym2 V) (W : Finset V) (F : Finset E)
    (hV : Valid ends W F) {x : E → ℝ} (hx : x ∈ Poly ends W F) :
    InHull (IsPM ends W F) x := by sorry
