-- Prove2me | Theorems.Thm_Nock_Verb_Den_subnode
-- name    : Nock.Verb.Den_subnode
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:15:36.756612+00:00
-- url     : https://prove2.me/theorems/56f26cca-54f4-472f-8e0a-40a6b308088e
-- title:
--   Verb: Den subnode
-- statement:
--   The Verb construction uses the Den subnode property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/PureCompleteHint.lean#L128-L133
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/PureCompleteHint.lean#L128-L133

module
public import Definitions.Def_LeanPool_PureNock_PureComplete
public import Mathlib.Tactic.IntervalCases
public import Definitions.Def_LeanPool_PureNock_PureCompleteHint
set_option autoImplicit true
@[expose] public section
public section
open Nock
open Nock.Verb
open Noun

theorem Nock.Verb.Den_subnode {v : Verb} {x : Noun} (hok : editOk v = true) (hv : Den v x)
    {i : Nat} {sub : Verb} (hmap : map i v = some sub) : ∃ y, Den sub y := by sorry
