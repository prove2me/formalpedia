-- Prove2me | Theorems.Thm_Nock_Verb_vcost_terminal
-- name    : Nock.Verb.vcost_terminal
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:03:53.238101+00:00
-- url     : https://prove2.me/theorems/bdc99dea-4083-4603-8801-60a9c4b7f8b8
-- title:
--   Verb: vcost terminal
-- statement:
--   `vcost` of a terminal verb is `0`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/PureAgreement.lean#L1924-L1934
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/PureAgreement.lean#L1924-L1934

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

theorem Nock.Verb.vcost_terminal : ∀ (v : Verb), isTerminal v = true → ∀ F, vcost F v = 0 := by sorry
