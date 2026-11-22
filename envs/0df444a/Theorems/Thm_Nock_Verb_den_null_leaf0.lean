-- Prove2me | Theorems.Thm_Nock_Verb_den_null_leaf0
-- name    : Nock.Verb.den_null_leaf0
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:15:50.087818+00:00
-- url     : https://prove2.me/theorems/47397886-d315-4799-bd7f-a79f90dc7db0
-- title:
--   Verb: den null leaf0
-- statement:
--   The Verb construction uses the den null leaf0 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/PureCompleteHint.lean#L232-L238
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/PureCompleteHint.lean#L232-L238

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

theorem Nock.Verb.den_null_leaf0 {inner : Verb} {f : Nat} {dv : Noun}
    (h : den (f + 1) (Verb.node .null (Verb.leaf 0) inner) = some dv) :
    ∃ w, dv = Noun.cell (Noun.atom 0) w := by sorry
