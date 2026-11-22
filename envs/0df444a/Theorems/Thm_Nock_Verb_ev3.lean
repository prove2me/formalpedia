-- Prove2me | Theorems.Thm_Nock_Verb_ev3
-- name    : Nock.Verb.ev3
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:11:23.793491+00:00
-- url     : https://prove2.me/theorems/39314728-5e5c-4a5b-8c70-3e91c33fc38d
-- title:
--   Verb: ev3
-- statement:
--   The Verb construction uses the ev3 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/Agreement.lean#L297-L301
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/Agreement.lean#L297-L301

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

theorem Nock.Verb.ev3 {s1 f1 x1 s2 f2 x2 s3 f3 x3} (h1 : Ev s1 f1 x1) (h2 : Ev s2 f2 x2) (h3 : Ev s3 f3 x3) :
    ∃ f, evalN f s1 f1 = some x1 ∧ evalN f s2 f2 = some x2 ∧ evalN f s3 f3 = some x3 := by sorry
