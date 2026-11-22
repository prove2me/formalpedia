-- Prove2me | Theorems.Thm_Nock_Verb_den_mono
-- name    : Nock.Verb.den_mono
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:01:06.531076+00:00
-- url     : https://prove2.me/theorems/19ea2a9d-dff7-4387-b442-0f5047d9ea50
-- title:
--   Verb: den mono
-- statement:
--   The Verb construction uses the den mono property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/Agreement.lean#L80-L84
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/Agreement.lean#L80-L84

module
public import Definitions.Def_LeanPool_PureNock_Verb
public import Definitions.Def_LeanPool_PureNock_Semantics
public import Definitions.Def_LeanPool_PureNock_Agreement
set_option autoImplicit true
@[expose] public section
public section
open Nock
open Nock.Verb
open Noun

theorem Nock.Verb.den_mono {n m : Nat} {v : Verb} {r : Noun}
    (hle : n ≤ m) (h : den n v = some r) : den m v = some r := by sorry
