-- Prove2me | Theorems.Thm_Nock_Verb_den_stepP
-- name    : Nock.Verb.den_stepP
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:08:32.958797+00:00
-- url     : https://prove2.me/theorems/2c2f7c9d-a38d-4110-a4fd-b1abb1cb8194
-- title:
--   Verb: den step P
-- statement:
--   The Verb construction uses the den step P property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/PureAgreement.lean#L1521-L1534
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/PureAgreement.lean#L1521-L1534

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

theorem Nock.Verb.den_stepP {v v' : Verb} (hwf : editOk v = true) (h : next v = some v') {r : Noun} :
    (∃ fuel, denP fuel v = some r) ↔ (∃ fuel, denP fuel v' = some r) := by sorry
