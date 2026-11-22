-- Prove2me | Theorems.Thm_Nock_Verb_slot_three_atom
-- name    : Nock.Verb.slot_three_atom
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:07:25.873683+00:00
-- url     : https://prove2.me/theorems/5439d07c-e237-4bf1-bf15-9022f03b6433
-- title:
--   Verb: slot three atom
-- statement:
--   The Verb construction uses the slot three atom property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/Agreement.lean#L589-L589
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/Agreement.lean#L589-L589

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

theorem Nock.Verb.slot_three_atom {k : Nat} : Noun.slot 3 (.atom k) = none := by sorry
