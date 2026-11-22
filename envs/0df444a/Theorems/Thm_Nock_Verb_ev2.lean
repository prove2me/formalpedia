-- Prove2me | Theorems.Thm_Nock_Verb_ev2
-- name    : Nock.Verb.ev2
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:00:45.435022+00:00
-- url     : https://prove2.me/theorems/fa20e4d4-4a59-4eda-b86d-2720aa43adf3
-- title:
--   Verb: ev2
-- statement:
--   The Verb construction uses the ev2 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/Agreement.lean#L292-L295
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/Agreement.lean#L292-L295

module
public import Definitions.Def_LeanPool_PureNock_Verb
public import Definitions.Def_LeanPool_PureNock_Semantics
public import Definitions.Def_LeanPool_PureNock_Agreement
set_option autoImplicit true
@[expose] public section
public section
open Nock
open Nock.Verb
open Noun

theorem Nock.Verb.ev2 {s1 f1 x1 s2 f2 x2} (h1 : Ev s1 f1 x1) (h2 : Ev s2 f2 x2) :
    ∃ f, evalN f s1 f1 = some x1 ∧ evalN f s2 f2 = some x2 := by sorry
