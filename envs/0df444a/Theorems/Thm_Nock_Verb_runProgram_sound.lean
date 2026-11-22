-- Prove2me | Theorems.Thm_Nock_Verb_runProgram_sound
-- name    : Nock.Verb.runProgram_sound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:21:17.768662+00:00
-- url     : https://prove2.me/theorems/972695f7-24d7-4921-bfaf-864264d5b9f2
-- title:
--   Verb: run Program sound
-- statement:
--   The Verb construction uses the run Program sound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/Agreement.lean#L1414-L1417
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/Agreement.lean#L1414-L1417

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

theorem Nock.Verb.runProgram_sound {s f r : Noun} {fuel : Nat}
    (h : runProgram fuel s f = some r) : ∃ fuel', evalN fuel' s f = some r := by sorry
