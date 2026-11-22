-- Prove2me | Theorems.Thm_Nock_Verb_Den_star
-- name    : Nock.Verb.Den_star
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:02:18.969807+00:00
-- url     : https://prove2.me/theorems/41abf5b1-af5e-4c7b-902c-ac58c27df548
-- title:
--   Verb: Den star
-- statement:
--   The Verb construction uses the Den star property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/Agreement.lean#L187-L208
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/Agreement.lean#L187-L208

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

theorem Nock.Verb.Den_star {l r x} : Den (.node .star l r) x ↔ ∃ a b, Den l a ∧ Den r b ∧ Ev a b x := by sorry
