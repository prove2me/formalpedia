-- Prove2me | Theorems.Thm_MatchingPolytope_Multi_eval_sum_smul_chi
-- name    : MatchingPolytope.Multi.eval_sum_smul_chi
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T23:25:36.868238+00:00
-- url     : https://prove2.me/theorems/50341215-2a53-4ee1-933b-03d03aa877e6
-- title:
--   Multi: eval sum smul chi
-- statement:
--   The Multi construction uses the eval sum smul chi property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/edmonds-matching-polytope/blob/6198b8314ac88a5638120fcf15d5b58c024caaab/MatchingPolytope/Glue.lean#L181-L183
-- source:
--   https://github.com/jtraverso/edmonds-matching-polytope/blob/6198b8314ac88a5638120fcf15d5b58c024caaab/MatchingPolytope/Glue.lean#L181-L183

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

theorem MatchingPolytope.Multi.eval_sum_smul_chi [Fintype E] (w : Finset E → ℝ) (e : E) :
    (∑ M, w M • chi M) e = ∑ M, w M * chi M e := by sorry
