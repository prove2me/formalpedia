-- Prove2me | Theorems.Thm_MatchingPolytope_convex_poly
-- name    : MatchingPolytope.convex_poly
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T23:27:47.982127+00:00
-- url     : https://prove2.me/theorems/fe19705b-49fd-4195-ba31-0b557a1ac78c
-- title:
--   Matching Polytope: convex poly
-- statement:
--   The Matching Polytope construction uses the convex poly property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/edmonds-matching-polytope/blob/6198b8314ac88a5638120fcf15d5b58c024caaab/MatchingPolytope/PerfectMatchingPolytope.lean#L30-L47
-- source:
--   https://github.com/jtraverso/edmonds-matching-polytope/blob/6198b8314ac88a5638120fcf15d5b58c024caaab/MatchingPolytope/PerfectMatchingPolytope.lean#L30-L47

module
public import Definitions.Def_MatchingPolytope_Defs
public import Definitions.Def_MatchingPolytope_Induction
public import Definitions.Def_MatchingPolytope_PerfectMatchingPolytope
set_option autoImplicit true
@[expose] public section
public section
open MatchingPolytope
open Finset Multi
variable {V E : Type*}

theorem MatchingPolytope.convex_poly (ends : E → Sym2 V) (W : Finset V) (F : Finset E) :
    Convex ℝ (Multi.Poly ends W F) := by sorry
