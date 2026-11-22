-- Prove2me | Theorems.Thm_Nock_evalN_mono
-- name    : Nock.evalN_mono
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:00:59.906624+00:00
-- url     : https://prove2.me/theorems/aa5f4273-46ac-4f7c-b635-6e6f093075e8
-- title:
--   Nock: eval N mono
-- statement:
--   The Nock construction uses the eval N mono property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/Semantics.lean#L35-L39
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/Semantics.lean#L35-L39

module
public import Definitions.Def_LeanPool_PureNock_Reference
public import Definitions.Def_LeanPool_PureNock_Semantics
set_option autoImplicit true
@[expose] public section
public section
open Nock

theorem Nock.evalN_mono {n m : Nat} {s form r : Noun}
    (hle : n ≤ m) (h : evalN n s form = some r) : evalN m s form = some r := by sorry
