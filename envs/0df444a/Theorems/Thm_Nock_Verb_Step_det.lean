-- Prove2me | Theorems.Thm_Nock_Verb_Step_det
-- name    : Nock.Verb.Step.det
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:06:56.20786+00:00
-- url     : https://prove2.me/theorems/f8c126ad-5caf-4bfd-8765-47d8e2dc1700
-- title:
--   Step: det
-- statement:
--   The transition relation is deterministic: `next` is a function.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/Trace.lean#L31-L32
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/Trace.lean#L31-L32

module
public import Definitions.Def_LeanPool_PureNock_Verb
public import Batteries.Tactic.Alias
public import Definitions.Def_LeanPool_PureNock_Trace
public import Theorems.Thm_Nock_Verb_SelStep_det

set_option autoImplicit true
@[expose] public section
public section
open Nock
open Nock.Verb

theorem Nock.Verb.Step.det {a b b' : Verb} (h : Step a b) (h' : Step a b') : b = b' := by sorry
