-- Prove2me | Theorems.Thm_Nock_evalN_succ
-- name    : Nock.evalN_succ
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:01:49.171434+00:00
-- url     : https://prove2.me/theorems/4b12f282-7c06-4f29-a982-781200af90b7
-- title:
--   Nock: eval N succ
-- statement:
--   The Nock construction uses the eval N succ property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/Semantics.lean#L21-L33
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/Semantics.lean#L21-L33

module
public import Definitions.Def_LeanPool_PureNock_Reference
public import Definitions.Def_LeanPool_PureNock_Semantics
set_option autoImplicit true
@[expose] public section
public section
open Nock

theorem Nock.evalN_succ {n : Nat} {s form r : Noun}
    (h : evalN n s form = some r) : evalN (n + 1) s form = some r := by sorry
