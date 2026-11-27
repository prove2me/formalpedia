-- Prove2me | Theorems.Thm_MatchingPolytope_Multi_inHull_step
-- name    : MatchingPolytope.Multi.inHull_step
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T23:27:23.030539+00:00
-- url     : https://prove2.me/theorems/72f4d5e5-cb27-42d5-b768-08d153e3c36a
-- title:
--   Multi: in Hull step
-- statement:
--   The Multi construction uses the in Hull step property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/edmonds-matching-polytope/blob/6198b8314ac88a5638120fcf15d5b58c024caaab/MatchingPolytope/Induction.lean#L420-L466
-- source:
--   https://github.com/jtraverso/edmonds-matching-polytope/blob/6198b8314ac88a5638120fcf15d5b58c024caaab/MatchingPolytope/Induction.lean#L420-L466

module
public import Definitions.Def_MatchingPolytope_Glue
public import Definitions.Def_MatchingPolytope_Induction
set_option autoImplicit true
@[expose] public section
public section
open MatchingPolytope MatchingPolytope.Multi
open Finset
variable {V E : Type*} {ends : E → Sym2 V} {W : Finset V} {F : Finset E}

theorem MatchingPolytope.Multi.inHull_step [Fintype E]
    (IH : ∀ (ends' : E → Sym2 V) (W' : Finset V) (F' : Finset E),
      W'.card + F'.card < W.card + F.card → Valid ends' W' F' →
        ∀ x ∈ Poly ends' W' F', InHull (IsPM ends' W' F') x)
    (hV : Valid ends W F) {x : E → ℝ} (hx : x ∈ Poly ends W F) :
    InHull (IsPM ends W F) x := by sorry
