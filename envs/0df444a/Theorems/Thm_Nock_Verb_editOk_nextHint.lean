-- Prove2me | Theorems.Thm_Nock_Verb_editOk_nextHint
-- name    : Nock.Verb.editOk_nextHint
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:08:12.291115+00:00
-- url     : https://prove2.me/theorems/cd3861f9-5009-4bae-8f17-87357f233f79
-- title:
--   Verb: edit Ok next Hint
-- statement:
--   `editOk` is preserved by `nextHint` (the invariant discharging `denHint_step`).
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/PureAgreement.lean#L833-L844
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/PureAgreement.lean#L833-L844

module
public import Definitions.Def_LeanPool_PureNock_Agreement
public import Definitions.Def_LeanPool_PureNock_Trace
public import Definitions.Def_LeanPool_PureNock_PaperReference
public import Mathlib.Tactic.IntervalCases
public import Definitions.Def_LeanPool_PureNock_PureAgreement
set_option autoImplicit true
@[expose] public section
public section
open Nock
open Nock.Verb
open Noun

theorem Nock.Verb.editOk_nextHint {v v'} (h : nextHint v = some v') (hok : editOk v = true) :
    editOk v' = true := by sorry
