-- Prove2me | Theorems.Thm_Nock_Verb_nextROM_none_of_terminal
-- name    : Nock.Verb.nextROM_none_of_terminal
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:19:20.076676+00:00
-- url     : https://prove2.me/theorems/af54a728-8dba-43c2-b94f-3f4fb97edfed
-- title:
--   Verb: next ROM none of terminal
-- statement:
--   A terminal verb cannot take a ROM step either.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/Verb.lean#L861-L862
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/Verb.lean#L861-L862

module
public import Definitions.Def_LeanPool_PureNock_Tree
public import Definitions.Def_LeanPool_PureNock_Reference
public import Definitions.Def_LeanPool_PureNock_Verb
set_option autoImplicit true
@[expose] public section
public section
open Nock
open Nock.Verb

theorem Nock.Verb.nextROM_none_of_terminal {v : Verb} (h : isTerminal v = true) : nextROM v = none := by sorry
