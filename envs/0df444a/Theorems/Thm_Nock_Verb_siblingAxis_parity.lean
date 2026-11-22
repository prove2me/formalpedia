-- Prove2me | Theorems.Thm_Nock_Verb_siblingAxis_parity
-- name    : Nock.Verb.siblingAxis_parity
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:12:22.595176+00:00
-- url     : https://prove2.me/theorems/74aa1585-035b-4f32-9496-d9c4028c7934
-- title:
--   Verb: sibling Axis parity
-- statement:
--   A sibling has the opposite parity to its axis.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/Agreement.lean#L1464-L1479
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/Agreement.lean#L1464-L1479

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

theorem Nock.Verb.siblingAxis_parity (a : Nat) :
    ((siblingAxis (a + 2)) % 2 == 0) = !((a + 2) % 2 == 0) := by sorry
