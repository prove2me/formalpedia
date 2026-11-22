-- Prove2me | Theorems.Thm_Nock_Verb_ev3P
-- name    : Nock.Verb.ev3P
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:12:41.233119+00:00
-- url     : https://prove2.me/theorems/bb3bd671-5146-47c5-8fb0-51c24a71bb4f
-- title:
--   Verb: ev3 P
-- statement:
--   The Verb construction uses the ev3 P property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/PureAgreement.lean#L168-L174
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/PureAgreement.lean#L168-L174

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

theorem Nock.Verb.ev3P {s1 f1 x1 s2 f2 x2 s3 f3 x3}
    (h1 : EvP s1 f1 x1) (h2 : EvP s2 f2 x2) (h3 : EvP s3 f3 x3) :
    ∃ f, evalPaper f s1 f1 = some x1 ∧ evalPaper f s2 f2 = some x2 ∧ evalPaper f s3 f3 = some x3 := by sorry
