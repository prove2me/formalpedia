-- Prove2me | Theorems.Thm_Nock_Verb_nockCheck_frameAgree
-- name    : Nock.Verb.nockCheck_frameAgree
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:19:22.724784+00:00
-- url     : https://prove2.me/theorems/cd27ee98-af8d-47eb-9ae7-0b468ee8469b
-- title:
--   Verb: nock Check frame Agree
-- statement:
--   **Accepted steps pass the frame gate (main.tex:1642).**  If `NockCheck` accepts a non-⊥
--       successor `b` of `a`, then `b` agrees with `a` outside the selected index: `FrameAgree`.
--       (The genuine-step branch of `NockCheck` is exactly the frame-preserving splice.)
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/Verb.lean#L996-L1003
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/Verb.lean#L996-L1003

module
public import Definitions.Def_LeanPool_PureNock_Tree
public import Definitions.Def_LeanPool_PureNock_Reference
public import Definitions.Def_LeanPool_PureNock_Verb
set_option autoImplicit true
@[expose] public section
public section
open Nock
open Nock.Verb

theorem Nock.Verb.nockCheck_frameAgree {a b : Verb} (h : NockCheck a (some b) = true) :
    ∃ i, getIndex a = some i ∧ FrameAgree i a b := by sorry
