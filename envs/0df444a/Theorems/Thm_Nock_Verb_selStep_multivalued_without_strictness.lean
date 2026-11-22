-- Prove2me | Theorems.Thm_Nock_Verb_selStep_multivalued_without_strictness
-- name    : Nock.Verb.selStep_multivalued_without_strictness
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:19:15.180831+00:00
-- url     : https://prove2.me/theorems/7a3a4ad0-5580-4e16-b4a3-2c6e9a93ac5a
-- title:
--   Verb: sel Step multivalued without strictness
-- statement:
--   **Non-vacuity of strictness.**  Under a non-strict order, `SelStep` is not a function:
--       it relates `twoRedex` to two distinct successors.  Contrast `SelStep.det`, which uses
--       `StrictSelect.total` to collapse exactly this ambiguity.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/Verb.lean#L689-L693
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/Verb.lean#L689-L693

module
public import Definitions.Def_LeanPool_PureNock_Tree
public import Definitions.Def_LeanPool_PureNock_Reference
public import Definitions.Def_LeanPool_PureNock_Verb
set_option autoImplicit true
@[expose] public section
public section
open Nock
open Nock.Verb

theorem Nock.Verb.selStep_multivalued_without_strictness :
    ∃ (a b b' : Verb), b ≠ b' ∧ SelStep emptyLt a b ∧ SelStep emptyLt a b' := by sorry
