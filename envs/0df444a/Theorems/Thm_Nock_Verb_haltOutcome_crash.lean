-- Prove2me | Theorems.Thm_Nock_Verb_haltOutcome_crash
-- name    : Nock.Verb.haltOutcome_crash
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:06:34.839024+00:00
-- url     : https://prove2.me/theorems/d41b1237-a841-45a0-86be-c8480e6feed6
-- title:
--   Verb: halt Outcome crash
-- statement:
--   A non-terminal halt is a `crash`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/Verb.lean#L1027-L1028
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/Verb.lean#L1027-L1028

module
public import Definitions.Def_LeanPool_PureNock_Tree
public import Definitions.Def_LeanPool_PureNock_Reference
public import Definitions.Def_LeanPool_PureNock_Verb
set_option autoImplicit true
@[expose] public section
public section
open Nock
open Nock.Verb

theorem Nock.Verb.haltOutcome_crash {v : Verb} (h : v.isTerminal = false) : haltOutcome v = .crash := by sorry
