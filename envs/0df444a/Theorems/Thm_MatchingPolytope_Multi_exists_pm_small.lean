-- Prove2me | Theorems.Thm_MatchingPolytope_Multi_exists_pm_small
-- name    : MatchingPolytope.Multi.exists_pm_small
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T23:27:17.422073+00:00
-- url     : https://prove2.me/theorems/8af10bcb-464c-445b-bcb9-29cc3efb1771
-- title:
--   Multi: exists pm small
-- statement:
--   The Multi construction uses the exists pm small property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/edmonds-matching-polytope/blob/6198b8314ac88a5638120fcf15d5b58c024caaab/MatchingPolytope/Induction.lean#L244-L353
-- source:
--   https://github.com/jtraverso/edmonds-matching-polytope/blob/6198b8314ac88a5638120fcf15d5b58c024caaab/MatchingPolytope/Induction.lean#L244-L353

module
public import Definitions.Def_MatchingPolytope_Glue
public import Definitions.Def_MatchingPolytope_Induction
set_option autoImplicit true
@[expose] public section
public section
open MatchingPolytope MatchingPolytope.Multi
open Finset
variable {V E : Type*} {ends : E → Sym2 V} {W : Finset V} {F : Finset E}

theorem MatchingPolytope.Multi.exists_pm_small (hV : Valid ends W F) {x : E → ℝ} (hx : x ∈ Poly ends W F)
    (hW4 : W.card ≤ 4) : ∃ M, IsPM ends W F M := by sorry
