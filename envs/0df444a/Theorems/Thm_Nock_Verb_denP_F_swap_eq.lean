-- Prove2me | Theorems.Thm_Nock_Verb_denP_F_swap_eq
-- name    : Nock.Verb.denP_F_swap_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:15:13.529801+00:00
-- url     : https://prove2.me/theorems/ae0057b0-8c42-4089-a1fd-349d2578d54b
-- title:
--   Verb: den P F swap eq
-- statement:
--   The Verb construction uses the den P F swap eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/PureComplete.lean#L949-L952
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/PureComplete.lean#L949-L952

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

theorem Nock.Verb.denP_F_swap_eq {F : Nat} {w w' : Verb} (hok : editOk w = true) (hrel : RelP w w')
    {a b : Noun} (ha : denP F w = some a) (hb : denP F w' = some b) : a = b := by sorry
