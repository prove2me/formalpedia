-- Prove2me | Theorems.Thm_Nock_Verb_Den_edit_node
-- name    : Nock.Verb.Den_edit_node
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:03:13.116333+00:00
-- url     : https://prove2.me/theorems/cae0689f-a3a1-4993-b87b-cd968ac2ce7b
-- title:
--   Verb: Den edit node
-- statement:
--   The Verb construction uses the Den edit node property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/Agreement.lean#L264-L278
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/Agreement.lean#L264-L278

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

theorem Nock.Verb.Den_edit_node {l b nw od x} : Den (.node .edit l (.node b nw od)) x ↔
    ∃ ax n o, Den l (.atom ax) ∧ Den nw n ∧ Den od o ∧ Noun.edit ax n o = some x := by sorry
