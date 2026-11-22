-- Prove2me | Theorems.Thm_Nock_Verb_eval_value_iff_run
-- name    : Nock.Verb.eval_value_iff_run
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:19:23.498809+00:00
-- url     : https://prove2.me/theorems/ae389af7-ae1b-4688-b89b-f46933ab7ef0
-- title:
--   Verb: eval value iff run
-- statement:
--   **Values are preserved exactly.**  `eval` yields `value r` at fuel `n` iff the `Option`-valued
--       `run` yields `some r` at the same fuel — successful evaluation is unchanged.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/Verb.lean#L1050-L1062
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/Verb.lean#L1050-L1062

module
public import Definitions.Def_LeanPool_PureNock_Tree
public import Definitions.Def_LeanPool_PureNock_Reference
public import Definitions.Def_LeanPool_PureNock_Verb
set_option autoImplicit true
@[expose] public section
public section
open Nock
open Nock.Verb

theorem Nock.Verb.eval_value_iff_run {n : Nat} {v : Verb} {r : Noun} :
    eval n v = .value r ↔ run n v = some r := by sorry
