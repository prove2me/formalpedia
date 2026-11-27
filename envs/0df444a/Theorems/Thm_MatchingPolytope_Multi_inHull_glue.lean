-- Prove2me | Theorems.Thm_MatchingPolytope_Multi_inHull_glue
-- name    : MatchingPolytope.Multi.inHull_glue
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T23:25:44.348622+00:00
-- url     : https://prove2.me/theorems/9539b0c7-ac36-5614-a183-2d5cc0ae5a42
-- title:
--   Multi: in Hull glue
-- statement:
--   The gluing step of Schrijver's proof.
--
--   Source: https://github.com/jtraverso/edmonds-matching-polytope/blob/6198b8314ac88a5638120fcf15d5b58c024caaab/MatchingPolytope/Glue.lean#L186-L309
-- source:
--   https://github.com/jtraverso/edmonds-matching-polytope/blob/6198b8314ac88a5638120fcf15d5b58c024caaab/MatchingPolytope/Glue.lean#L186-L309

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

theorem MatchingPolytope.Multi.inHull_glue [Fintype E] (hV : Valid ends W F) {x : E → ℝ} (hx : x ∈ Poly ends W F)
    (hpos : ∀ e ∈ F, 0 < x e) {S : Finset V} (hSW : S ⊆ W) {s t : V} (hs : s ∈ S)
    (ht : t ∈ W \ S)
    (h1 : InHull (IsPM (shrinkEnds ends S s) (shrinkW W S s) (shrinkF ends F S))
      (restr (shrinkF ends F S) x))
    (h2 : InHull (IsPM (shrinkEnds ends (W \ S) t) (shrinkW W (W \ S) t)
      (shrinkF ends F (W \ S))) (restr (shrinkF ends F (W \ S)) x)) :
    InHull (IsPM ends W F) x := by sorry
