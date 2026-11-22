-- Prove2me | Theorems.Thm_Nock_Verb_eval_crash_mono
-- name    : Nock.Verb.eval_crash_mono
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:10:20.361309+00:00
-- url     : https://prove2.me/theorems/489408b5-7aef-4dfe-aac8-3b6d41163eb1
-- title:
--   Verb: eval crash mono
-- statement:
--   **Crash is stable one step on**: if `eval` reports `crash` at fuel `n`, it reports `crash` at
--       `n + 1`.  (The general "any larger fuel" form is `eval_crash_mono_le`.)
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/Verb.lean#L1066-L1074
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/Verb.lean#L1066-L1074

module
public import Definitions.Def_LeanPool_PureNock_Tree
public import Definitions.Def_LeanPool_PureNock_Reference
public import Definitions.Def_LeanPool_PureNock_Verb
set_option autoImplicit true
@[expose] public section
public section
open Nock
open Nock.Verb

theorem Nock.Verb.eval_crash_mono {n : Nat} {v : Verb} (h : eval n v = .crash) :
    eval (n + 1) v = .crash := by sorry
