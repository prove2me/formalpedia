-- Prove2me | Theorems.Thm_Nock_Verb_EvN_op9
-- name    : Nock.Verb.EvN_op9
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:07:10.18713+00:00
-- url     : https://prove2.me/theorems/d96b546d-a15a-4cf2-a03c-cf433ffa67ad
-- title:
--   Verb: Ev N op9
-- statement:
--   The Verb construction uses the Ev N op9 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/Agreement.lean#L503-L532
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/Agreement.lean#L503-L532

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

theorem Nock.Verb.EvN_op9 {subj tail x} : Ev subj (.cell (.atom 9) tail) x ↔
    ∃ ax c core arm, tail = .cell (.atom ax) c ∧ Ev subj c core ∧
      Noun.slot ax core = some arm ∧ Ev core arm x := by sorry
