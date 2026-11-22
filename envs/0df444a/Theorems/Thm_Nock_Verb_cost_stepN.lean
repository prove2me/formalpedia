-- Prove2me | Theorems.Thm_Nock_Verb_cost_stepN
-- name    : Nock.Verb.cost_stepN
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:17:15.516415+00:00
-- url     : https://prove2.me/theorems/faf4dff7-f47a-4dc4-b176-71e201c9a16e
-- title:
--   Verb: cost step N
-- statement:
--   The Verb construction uses the cost step N property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/PureCompleteHint.lean#L1335-L1404
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/PureCompleteHint.lean#L1335-L1404

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

theorem Nock.Verb.cost_stepN {F : Nat} {v v' : Verb} {x x' : Noun}
    (hwf : editOk v = true) (hv : den F v = some x) (hv' : den F v' = some x')
    (h : nextHint v = some v') : vcostN F v' < vcostN F v := by sorry
