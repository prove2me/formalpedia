-- Prove2me | Theorems.Thm_Nock_Verb_DenP_null
-- name    : Nock.Verb.DenP_null
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:05:02.510428+00:00
-- url     : https://prove2.me/theorems/1af310a3-49b9-43ef-a57b-57724cc9ce90
-- title:
--   Verb: Den P null
-- statement:
--   The Verb construction uses the Den P null property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/PureAgreement.lean#L416-L434
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/PureAgreement.lean#L416-L434

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

theorem Nock.Verb.DenP_null {l r x} : DenP (.node .null l r) x ↔ ∃ a b, x = .cell a b ∧ DenP l a ∧ DenP r b := by sorry
