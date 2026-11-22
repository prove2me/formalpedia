-- Prove2me | Theorems.Thm_Nock_Verb_next_none_of_terminal
-- name    : Nock.Verb.next_none_of_terminal
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:04:11.884399+00:00
-- url     : https://prove2.me/theorems/7aa8f671-57f0-416d-acb4-c43844d6dd6f
-- title:
--   Verb: next none of terminal
-- statement:
--   A terminal verb cannot take a Nock step.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/Verb.lean#L722-L723
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/Verb.lean#L722-L723

module
public import Definitions.Def_LeanPool_PureNock_Tree
public import Definitions.Def_LeanPool_PureNock_Reference
public import Definitions.Def_LeanPool_PureNock_Verb
set_option autoImplicit true
@[expose] public section
public section
open Nock
open Nock.Verb

theorem Nock.Verb.next_none_of_terminal {v : Verb} (h : isTerminal v = true) : next v = none := by sorry
