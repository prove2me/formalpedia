-- Prove2me | Theorems.Thm_Nock_Verb_slot_three
-- name    : Nock.Verb.slot_three
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:01:10.940511+00:00
-- url     : https://prove2.me/theorems/8711ee21-6357-4892-b2c1-b512f85b4d27
-- title:
--   Verb: slot three
-- statement:
--   The Verb construction uses the slot three property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/Agreement.lean#L587-L587
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/Agreement.lean#L587-L587

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

theorem Nock.Verb.slot_three {a b : Noun} : Noun.slot 3 (.cell a b) = some b := by sorry
