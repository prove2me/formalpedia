-- Prove2me | Theorems.Thm_Nock_Verb_redexHint_eq_reduce_of_hintExpand_none
-- name    : Nock.Verb.redexHint_eq_reduce_of_hintExpand_none
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:15:29.990846+00:00
-- url     : https://prove2.me/theorems/73454aec-4193-4a2b-938d-91da826b7aa7
-- title:
--   Verb: redex Hint eq reduce of hint Expand none
-- statement:
--   The Verb construction uses the redex Hint eq reduce of hint Expand none property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/PureCompleteHint.lean#L49-L51
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/PureCompleteHint.lean#L49-L51

module
public import Definitions.Def_LeanPool_PureNock_PureComplete
public import Mathlib.Tactic.IntervalCases
public import Definitions.Def_LeanPool_PureNock_PureCompleteHint
set_option autoImplicit true
@[expose] public section
public section
open Nock
open Nock.Verb
open Noun

theorem Nock.Verb.redexHint_eq_reduce_of_hintExpand_none {v : Verb} (h : hintExpand v = none) :
    redexHint v = reduce v := by sorry
