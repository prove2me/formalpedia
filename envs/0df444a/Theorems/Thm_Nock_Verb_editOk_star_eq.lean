-- Prove2me | Theorems.Thm_Nock_Verb_editOk_star_eq
-- name    : Nock.Verb.editOk_star_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:07:21.213584+00:00
-- url     : https://prove2.me/theorems/d7cf33d6-ba89-4f3c-b245-0f50ba776547
-- title:
--   Verb: edit Ok star eq
-- statement:
--   The Verb construction uses the edit Ok star eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/Agreement.lean#L577-L577
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/Agreement.lean#L577-L577

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

theorem Nock.Verb.editOk_star_eq {l r} : editOk (.node .star l r) = (editOk l && editOk r) := by sorry
