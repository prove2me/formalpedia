-- Prove2me | Theorems.Thm_Nock_Verb_slot_one
-- name    : Nock.Verb.slot_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:02:25.322614+00:00
-- url     : https://prove2.me/theorems/f28bd4eb-723a-4c55-be75-20f5893e94c7
-- title:
--   Verb: slot one
-- statement:
--   The Verb construction uses the slot one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/Agreement.lean#L585-L585
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/Agreement.lean#L585-L585

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

theorem Nock.Verb.slot_one {n : Noun} : Noun.slot 1 n = some n := by sorry
