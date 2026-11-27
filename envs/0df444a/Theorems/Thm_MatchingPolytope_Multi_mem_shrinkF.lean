-- Prove2me | Theorems.Thm_MatchingPolytope_Multi_mem_shrinkF
-- name    : MatchingPolytope.Multi.mem_shrinkF
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T23:21:32.062048+00:00
-- url     : https://prove2.me/theorems/6576737f-c1d2-4804-91a5-38de67b580ac
-- title:
--   Multi: mem shrink F
-- statement:
--   The Multi construction uses the mem shrink F property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/edmonds-matching-polytope/blob/6198b8314ac88a5638120fcf15d5b58c024caaab/MatchingPolytope/Shrink.lean#L36-L39
-- source:
--   https://github.com/jtraverso/edmonds-matching-polytope/blob/6198b8314ac88a5638120fcf15d5b58c024caaab/MatchingPolytope/Shrink.lean#L36-L39

module
public import Definitions.Def_MatchingPolytope_Multigraph
public import Definitions.Def_MatchingPolytope_Shrink
set_option autoImplicit true
@[expose] public section
public section
open MatchingPolytope MatchingPolytope.Multi
open Finset
variable {V E : Type*}
variable {ends : E → Sym2 V} {F : Finset E}

theorem MatchingPolytope.Multi.mem_shrinkF {R : Finset V} {e : E} :
    e ∈ shrinkF ends F R ↔ e ∈ F ∧ ∃ u ∈ ends e, u ∉ R := by sorry
