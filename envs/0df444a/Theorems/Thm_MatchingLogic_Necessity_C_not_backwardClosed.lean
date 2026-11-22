-- Prove2me | Theorems.Thm_MatchingLogic_Necessity_C_not_backwardClosed
-- name    : MatchingLogic.Necessity.C_not_backwardClosed
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:33:10.345196+00:00
-- url     : https://prove2.me/theorems/fd1147b1-57e0-4dd0-a33f-c50ef11539e3
-- title:
--   Necessity: C not backward Closed
-- statement:
--   The Necessity construction uses the C not backward Closed property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/Necessity.lean#L49-L52
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/Necessity.lean#L49-L52

module
public import Definitions.Def_LeanPool_MatchingLogic_Locality
public import Mathlib.Data.Set.Insert
public import Definitions.Def_LeanPool_MatchingLogic_Necessity
set_option autoImplicit true
@[expose] public section
public section
open MatchingLogic
open MatchingLogic.Necessity

theorem MatchingLogic.Necessity.C_not_backwardClosed : ¬ M.BackwardClosed C := by sorry
