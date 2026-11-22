-- Prove2me | Theorems.Thm_Nock_Verb_siblingAxis_half
-- name    : Nock.Verb.siblingAxis_half
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:12:21.358327+00:00
-- url     : https://prove2.me/theorems/03097004-3c4c-4497-a431-7fa6d31d5c25
-- title:
--   Verb: sibling Axis half
-- statement:
--   A sibling shares its parent: `siblingAxis (a+2) / 2 = (a+2) / 2`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/Agreement.lean#L1453-L1461
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/Agreement.lean#L1453-L1461

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

theorem Nock.Verb.siblingAxis_half (a : Nat) : siblingAxis (a + 2) / 2 = (a + 2) / 2 := by sorry
