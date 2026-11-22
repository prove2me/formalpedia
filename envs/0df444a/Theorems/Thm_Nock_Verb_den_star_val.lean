-- Prove2me | Theorems.Thm_Nock_Verb_den_star_val
-- name    : Nock.Verb.den_star_val
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:15:45.527786+00:00
-- url     : https://prove2.me/theorems/d736348e-ef2a-4600-abdf-b3a21e8dac31
-- title:
--   Verb: den star val
-- statement:
--   The Verb construction uses the den star val property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/PureCompleteHint.lean#L218-L221
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/PureCompleteHint.lean#L218-L221

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

theorem Nock.Verb.den_star_val {A B : Verb} {f : Nat} {a b w : Noun}
    (hA : den f A = some a) (hB : den f B = some b) (he : evalN f a b = some w) :
    den (f + 1) (Verb.node .star A B) = some w := by sorry
