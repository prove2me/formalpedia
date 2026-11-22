-- Prove2me | Theorems.Thm_Nock_Verb_Den_terminal_iff
-- name    : Nock.Verb.Den_terminal_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:01:09.452155+00:00
-- url     : https://prove2.me/theorems/b93ecc57-f8d9-4b1e-a172-87700807fd09
-- title:
--   Verb: Den terminal iff
-- statement:
--   The Verb construction uses the Den terminal iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/Agreement.lean#L542-L545
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/Agreement.lean#L542-L545

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

theorem Nock.Verb.Den_terminal_iff {v x} (ht : isTerminal v = true) : Den v x ↔ x = v.noun := by sorry
