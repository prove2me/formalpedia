-- Prove2me | Theorems.Thm_Nock_Verb_evalN_atom_none
-- name    : Nock.Verb.evalN_atom_none
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:15:22.746801+00:00
-- url     : https://prove2.me/theorems/18a5357e-1a5c-4503-a322-9290bddae3a4
-- title:
--   Verb: eval N atom none
-- statement:
--   The Verb construction uses the eval N atom none property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/PureCompleteHint.lean#L32-L33
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/PureCompleteHint.lean#L32-L33

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

theorem Nock.Verb.evalN_atom_none (f : Nat) (s : Noun) (k : Nat) : evalN f s (.atom k) = none := by sorry
