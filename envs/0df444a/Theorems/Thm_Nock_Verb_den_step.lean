-- Prove2me | Theorems.Thm_Nock_Verb_den_step
-- name    : Nock.Verb.den_step
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:12:17.883999+00:00
-- url     : https://prove2.me/theorems/a859559e-4498-4f1f-915f-ee56dc2205f8
-- title:
--   Verb: den step
-- statement:
--   The Verb construction uses the den step property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/Agreement.lean#L1377-L1390
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/Agreement.lean#L1377-L1390

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

theorem Nock.Verb.den_step {v v' : Verb} (hwf : editOk v = true) (h : next v = some v') {r : Noun} :
    (∃ fuel, den fuel v = some r) ↔ (∃ fuel, den fuel v' = some r) := by sorry
