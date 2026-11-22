-- Prove2me | Theorems.Thm_Nock_Verb_getIndex_none_iff_terminal
-- name    : Nock.Verb.getIndex_none_iff_terminal
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:02:58.885323+00:00
-- url     : https://prove2.me/theorems/6ef1b4fb-f153-4221-9248-f215f447f163
-- title:
--   Verb: get Index none iff terminal
-- statement:
--   **`getIndex` is `none` iff terminal.**  The `←` is `getIndex_none_of_terminal`; the `→`
--       is `terminal_of_enum_nonpending` fed the `maximumPendingIndex` emptiness spec.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/Verb.lean#L762-L768
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/Verb.lean#L762-L768

module
public import Definitions.Def_LeanPool_PureNock_Tree
public import Definitions.Def_LeanPool_PureNock_Reference
public import Definitions.Def_LeanPool_PureNock_Verb
set_option autoImplicit true
@[expose] public section
public section
open Nock
open Nock.Verb

theorem Nock.Verb.getIndex_none_iff_terminal {v : Verb} : getIndex v = none ↔ isTerminal v = true := by sorry
