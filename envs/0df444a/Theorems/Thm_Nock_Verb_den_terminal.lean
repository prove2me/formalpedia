-- Prove2me | Theorems.Thm_Nock_Verb_den_terminal
-- name    : Nock.Verb.den_terminal
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:04:17.110571+00:00
-- url     : https://prove2.me/theorems/6fd16ac8-523b-49b0-a8b6-b1e29b423bf3
-- title:
--   Verb: den terminal
-- statement:
--   Terminal verbs denote their underlying noun (given adequate fuel).
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/Agreement.lean#L101-L116
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/Agreement.lean#L101-L116

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

theorem Nock.Verb.den_terminal : ∀ (v : Verb) (fuel : Nat),
    isTerminal v = true → v.noun.size ≤ fuel → den fuel v = some v.noun := by sorry
