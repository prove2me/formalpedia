-- Prove2me | Theorems.Thm_Nock_Verb_runTrace_adjNockCheckB
-- name    : Nock.Verb.runTrace_adjNockCheckB
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:29:42.945173+00:00
-- url     : https://prove2.me/theorems/9c427e6f-e228-41d3-b3ae-0692bb277e4f
-- title:
--   Verb: run Trace adj Nock Check B
-- statement:
--   **The executable checker accepts every emitted trace.**  Running `adjNockCheckB` on the
--       output of `runTrace` returns `true` — the certificate is machine-checkable, not just a
--       `Prop`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/TraceCertificate.lean#L136-L138
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/TraceCertificate.lean#L136-L138

module
public import Definitions.Def_LeanPool_PureNock_Trace
public import Definitions.Def_LeanPool_PureNock_TraceCertificate
set_option autoImplicit true
@[expose] public section
public section
open Nock
open Nock.Verb

theorem Nock.Verb.runTrace_adjNockCheckB {fuel : Nat} {v : Verb} {T : List Verb}
    (h : runTrace fuel v = some T) : adjNockCheckB T = true := by sorry
