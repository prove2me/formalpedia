-- Prove2me | Theorems.Thm_Nock_Verb_run_soundP
-- name    : Nock.Verb.run_soundP
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:14:03.679797+00:00
-- url     : https://prove2.me/theorems/80bf7747-88ac-4bb5-b122-ae3392fc17ce
-- title:
--   Verb: run sound P
-- statement:
--   The Verb construction uses the run sound P property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/PureAgreement.lean#L1536-L1556
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/PureAgreement.lean#L1536-L1556

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

theorem Nock.Verb.run_soundP {v : Verb} {r : Noun} :
    ∀ fuel, editOk v = true → run fuel v = some r → (∃ f, denP f v = some r) := by sorry
