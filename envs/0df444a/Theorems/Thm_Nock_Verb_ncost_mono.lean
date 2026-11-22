-- Prove2me | Theorems.Thm_Nock_Verb_ncost_mono
-- name    : Nock.Verb.ncost_mono
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:15:54.369836+00:00
-- url     : https://prove2.me/theorems/b5584109-265e-45a5-bf55-44b133264c47
-- title:
--   Verb: ncost mono
-- statement:
--   The Verb construction uses the ncost mono property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/PureCompleteHint.lean#L341-L345
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/PureCompleteHint.lean#L341-L345

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

theorem Nock.Verb.ncost_mono {n m : Nat} {a b r : Noun} (hle : n ≤ m) (hb : evalN n a b = some r) :
    ncost m a b = ncost n a b := by sorry
