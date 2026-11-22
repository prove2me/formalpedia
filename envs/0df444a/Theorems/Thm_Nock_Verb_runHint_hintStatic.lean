-- Prove2me | Theorems.Thm_Nock_Verb_runHint_hintStatic
-- name    : Nock.Verb.runHint_hintStatic
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:08:15.531229+00:00
-- url     : https://prove2.me/theorems/913e8aaa-4693-449e-9d8a-aa513a623171
-- title:
--   Verb: run Hint hint Static
-- statement:
--   The Verb construction uses the run Hint hint Static property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/PureAgreement.lean#L957-L959
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/PureAgreement.lean#L957-L959

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

theorem Nock.Verb.runHint_hintStatic : runHintProgram 32 (Noun.atom 42) hintProgStatic = some (Noun.atom 42)
  := by sorry
