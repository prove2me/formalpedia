-- Prove2me | Theorems.Thm_Nock_Verb_den_localP
-- name    : Nock.Verb.den_localP
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:08:28.550517+00:00
-- url     : https://prove2.me/theorems/19ad384b-119d-44b6-9474-9c17100471bd
-- title:
--   Verb: den local P
-- statement:
--   The Verb construction uses the den local P property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/PureAgreement.lean#L1514-L1519
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/PureAgreement.lean#L1514-L1519

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

theorem Nock.Verb.den_localP {sub r₀ x} (hd : inDomain sub = true) (hr : reduce sub = some r₀) :
    (DenP sub x ↔ DenP r₀ x) := by sorry
