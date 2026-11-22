-- Prove2me | Theorems.Thm_Nock_Verb_DenP_edit_node
-- name    : Nock.Verb.DenP_edit_node
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:03:44.701717+00:00
-- url     : https://prove2.me/theorems/50a6f5db-7786-42eb-83fc-c215fb0d8f40
-- title:
--   Verb: Den P edit node
-- statement:
--   The Verb construction uses the Den P edit node property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/PureAgreement.lean#L513-L527
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/PureAgreement.lean#L513-L527

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

theorem Nock.Verb.DenP_edit_node {l b nw od x} : DenP (.node .edit l (.node b nw od)) x ↔
    ∃ ax n o, DenP l (.atom ax) ∧ DenP nw n ∧ DenP od o ∧ Noun.edit ax n o = some x := by sorry
