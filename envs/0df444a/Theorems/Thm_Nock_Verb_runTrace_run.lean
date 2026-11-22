-- Prove2me | Theorems.Thm_Nock_Verb_runTrace_run
-- name    : Nock.Verb.runTrace_run
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:29:44.253357+00:00
-- url     : https://prove2.me/theorems/46947c47-ea81-4ba1-b54d-860dc9bfaea6
-- title:
--   Verb: run Trace run
-- statement:
--   **The emitted trace's last verb carries exactly the `run` result.**  `run fuel v` is the
--       `result` (terminal noun, or `none` on crash) of the trace's final verb.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/TraceCertificate.lean#L144-L173
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/TraceCertificate.lean#L144-L173

module
public import Definitions.Def_LeanPool_PureNock_Trace
public import Definitions.Def_LeanPool_PureNock_TraceCertificate
set_option autoImplicit true
@[expose] public section
public section
open Nock
open Nock.Verb

theorem Nock.Verb.runTrace_run :
    ∀ (fuel : Nat) (v : Verb) (T : List Verb), runTrace fuel v = some T →
      ∃ w, T.getLast? = some w ∧ run fuel v = result w := by sorry
