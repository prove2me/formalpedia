-- Prove2me | Theorems.Thm_Nock_Verb_getIndex_none_of_terminal
-- name    : Nock.Verb.getIndex_none_of_terminal
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:02:55.595802+00:00
-- url     : https://prove2.me/theorems/e546c3ee-f7d9-4326-9436-11a858f24516
-- title:
--   Verb: get Index none of terminal
-- statement:
--   `getIndex` of a terminal verb is `none`: no internal node carries a pending action.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/Verb.lean#L715-L718
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/Verb.lean#L715-L718

module
public import Definitions.Def_LeanPool_PureNock_Tree
public import Definitions.Def_LeanPool_PureNock_Reference
public import Definitions.Def_LeanPool_PureNock_Verb
set_option autoImplicit true
@[expose] public section
public section
open Nock
open Nock.Verb

theorem Nock.Verb.getIndex_none_of_terminal {v : Verb} (h : isTerminal v = true) : getIndex v = none := by sorry
