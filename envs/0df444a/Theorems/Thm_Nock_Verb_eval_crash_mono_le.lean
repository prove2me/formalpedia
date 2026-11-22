-- Prove2me | Theorems.Thm_Nock_Verb_eval_crash_mono_le
-- name    : Nock.Verb.eval_crash_mono_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:19:27.726805+00:00
-- url     : https://prove2.me/theorems/9afce61b-a519-4dbe-8ebb-d2d55445b9d2
-- title:
--   Verb: eval crash mono le
-- statement:
--   **Crash is permanent** (so a single successful `eval` certifies it *at every fuel*): once `eval`
--       reports `crash` at fuel `n`, it reports `crash` at every `m ≥ n`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/Verb.lean#L1078-L1082
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/Verb.lean#L1078-L1082

module
public import Definitions.Def_LeanPool_PureNock_Tree
public import Definitions.Def_LeanPool_PureNock_Reference
public import Definitions.Def_LeanPool_PureNock_Verb
set_option autoImplicit true
@[expose] public section
public section
open Nock
open Nock.Verb

theorem Nock.Verb.eval_crash_mono_le {n m : Nat} {v : Verb} (hnm : n ≤ m) (h : eval n v = .crash) :
    eval m v = .crash := by sorry
