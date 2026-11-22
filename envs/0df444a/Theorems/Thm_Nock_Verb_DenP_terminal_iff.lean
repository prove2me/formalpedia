-- Prove2me | Theorems.Thm_Nock_Verb_DenP_terminal_iff
-- name    : Nock.Verb.DenP_terminal_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:02:10.163538+00:00
-- url     : https://prove2.me/theorems/704010b7-f27a-4637-bf71-aa6a3966504c
-- title:
--   Verb: Den P terminal iff
-- statement:
--   The Verb construction uses the Den P terminal iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/PureAgreement.lean#L541-L544
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/PureAgreement.lean#L541-L544

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

theorem Nock.Verb.DenP_terminal_iff {v x} (ht : isTerminal v = true) : DenP v x ↔ x = v.noun := by sorry
