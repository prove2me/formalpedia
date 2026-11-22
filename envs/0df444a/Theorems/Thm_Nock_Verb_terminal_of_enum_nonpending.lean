-- Prove2me | Theorems.Thm_Nock_Verb_terminal_of_enum_nonpending
-- name    : Nock.Verb.terminal_of_enum_nonpending
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:06:32.781068+00:00
-- url     : https://prove2.me/theorems/13912347-7f6a-4856-b64f-f8d8fd6bed12
-- title:
--   Verb: terminal of enum nonpending
-- statement:
--   **Converse of `enum_nonpending_of_terminal`.**  If every internal node enumerated from `v`
--       is non-pending, then `v` is terminal.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/Verb.lean#L729-L757
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/Verb.lean#L729-L757

module
public import Definitions.Def_LeanPool_PureNock_Tree
public import Definitions.Def_LeanPool_PureNock_Reference
public import Definitions.Def_LeanPool_PureNock_Verb
set_option autoImplicit true
@[expose] public section
public section
open Nock
open Nock.Verb

theorem Nock.Verb.terminal_of_enum_nonpending :
    ∀ (v : Verb) (c : Nat),
      (∀ p ∈ (enum v c).2, p.2.isPending = false) → isTerminal v = true := by sorry
