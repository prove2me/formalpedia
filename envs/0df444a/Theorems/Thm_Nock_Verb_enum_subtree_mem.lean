-- Prove2me | Theorems.Thm_Nock_Verb_enum_subtree_mem
-- name    : Nock.Verb.enum_subtree_mem
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:10:15.368208+00:00
-- url     : https://prove2.me/theorems/c192c621-a29f-49eb-9a3c-02c08163269b
-- title:
--   Verb: enum subtree mem
-- statement:
--   **Subtree enumeration embeds.**  If `sub` is enumerated at index `i` within `v` (counter
--       `c`), then every internal node of `sub`'s own enumeration (counter `i`) also appears in
--       `v`'s enumeration.  This is what lets a pending node *inside* the selected redex be seen as
--       a pending index of the whole verb.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/Verb.lean#L774-L792
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/Verb.lean#L774-L792

module
public import Definitions.Def_LeanPool_PureNock_Tree
public import Definitions.Def_LeanPool_PureNock_Reference
public import Definitions.Def_LeanPool_PureNock_Verb
set_option autoImplicit true
@[expose] public section
public section
open Nock
open Nock.Verb

theorem Nock.Verb.enum_subtree_mem :
    ∀ (v : Verb) (c i : Nat) (sub : Verb),
      (i, sub) ∈ (enum v c).2 → ∀ p ∈ (enum sub i).2, p ∈ (enum v c).2 := by sorry
