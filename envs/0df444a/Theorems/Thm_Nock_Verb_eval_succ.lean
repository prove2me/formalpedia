-- Prove2me | Theorems.Thm_Nock_Verb_eval_succ
-- name    : Nock.Verb.eval_succ
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:02:08.617774+00:00
-- url     : https://prove2.me/theorems/502b15b1-3fa7-4033-b73f-e16c6de95ead
-- title:
--   Verb: eval succ
-- statement:
--   One-step unfolding of `eval` (definitional), to avoid over-unfolding nested `eval` calls.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/Verb.lean#L1045-L1046
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/Verb.lean#L1045-L1046

module
public import Definitions.Def_LeanPool_PureNock_Tree
public import Definitions.Def_LeanPool_PureNock_Reference
public import Definitions.Def_LeanPool_PureNock_Verb
set_option autoImplicit true
@[expose] public section
public section
open Nock
open Nock.Verb

theorem Nock.Verb.eval_succ (n : Nat) (v : Verb) :
    eval (n + 1) v = match next v with | some v' => eval n v' | none => haltOutcome v := by sorry
