-- Prove2me | Theorems.Thm_Nock_Verb_run_sound
-- name    : Nock.Verb.run_sound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:12:19.465189+00:00
-- url     : https://prove2.me/theorems/6717ed89-6e42-482d-b538-bc66acf36eb8
-- title:
--   Verb: run sound
-- statement:
--   The Verb construction uses the run sound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/Agreement.lean#L1392-L1412
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/Agreement.lean#L1392-L1412

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

theorem Nock.Verb.run_sound {v : Verb} {r : Noun} :
    ∀ fuel, editOk v = true → run fuel v = some r → (∃ f, den f v = some r) := by sorry
