-- Prove2me | Theorems.Thm_Nock_Verb_editOk_redexHint
-- name    : Nock.Verb.editOk_redexHint
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:08:09.709801+00:00
-- url     : https://prove2.me/theorems/1313e40b-27bd-43e0-8ac8-21a4eb31405a
-- title:
--   Verb: edit Ok redex Hint
-- statement:
--   `editOk` is preserved by the extended local rewrite.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/PureAgreement.lean#L793-L802
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/PureAgreement.lean#L793-L802

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

theorem Nock.Verb.editOk_redexHint {sub r₀} (hr : redexHint sub = some r₀) (hok : editOk sub = true) :
    editOk r₀ = true := by sorry
