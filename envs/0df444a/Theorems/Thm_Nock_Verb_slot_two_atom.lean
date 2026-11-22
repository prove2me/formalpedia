-- Prove2me | Theorems.Thm_Nock_Verb_slot_two_atom
-- name    : Nock.Verb.slot_two_atom
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:07:23.588622+00:00
-- url     : https://prove2.me/theorems/a3014e6a-0173-439f-8e5b-a2f414a82967
-- title:
--   Verb: slot two atom
-- statement:
--   The Verb construction uses the slot two atom property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/Agreement.lean#L588-L588
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/Agreement.lean#L588-L588

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

theorem Nock.Verb.slot_two_atom {k : Nat} : Noun.slot 2 (.atom k) = none := by sorry
