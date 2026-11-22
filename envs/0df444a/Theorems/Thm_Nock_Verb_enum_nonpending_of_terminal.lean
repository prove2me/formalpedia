-- Prove2me | Theorems.Thm_Nock_Verb_enum_nonpending_of_terminal
-- name    : Nock.Verb.enum_nonpending_of_terminal
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:06:33.435128+00:00
-- url     : https://prove2.me/theorems/d3146845-9dc6-422a-a28d-23d76f834d95
-- title:
--   Verb: enum nonpending of terminal
-- statement:
--   Every internal node produced by `enum` of a *terminal* verb is non-pending.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/Verb.lean#L698-L711
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/Verb.lean#L698-L711

module
public import Definitions.Def_LeanPool_PureNock_Tree
public import Definitions.Def_LeanPool_PureNock_Reference
public import Definitions.Def_LeanPool_PureNock_Verb
set_option autoImplicit true
@[expose] public section
public section
open Nock
open Nock.Verb

theorem Nock.Verb.enum_nonpending_of_terminal : ∀ (v : Verb), isTerminal v = true →
    ∀ (c : Nat), ∀ p ∈ (enum v c).2, p.2.isPending = false := by sorry
