-- Prove2me | Theorems.Thm_Nock_Verb_denP_null_none
-- name    : Nock.Verb.denP_null_none
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:14:44.037745+00:00
-- url     : https://prove2.me/theorems/692e251b-50cf-4b43-950a-ef484549776e
-- title:
--   Verb: den P null none
-- statement:
--   The Verb construction uses the den P null none property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/PureComplete.lean#L112-L114
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/PureComplete.lean#L112-L114

module
public import Definitions.Def_LeanPool_PureNock_PureAgreement
public import Mathlib.Tactic.IntervalCases
public import Definitions.Def_LeanPool_PureNock_PureComplete
set_option autoImplicit true
@[expose] public section
public section
open Nock
open Nock.Verb
open Noun

theorem Nock.Verb.denP_null_none {A B : Verb} {f : Nat} (hA : denP f A = none) :
    denP (f + 1) (Verb.node .null A B) = none := by sorry
