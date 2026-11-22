-- Prove2me | Theorems.Thm_Nock_Verb_runTrace_traceOf
-- name    : Nock.Verb.runTrace_traceOf
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:09:49.411906+00:00
-- url     : https://prove2.me/theorems/284f0bd1-ff4b-48bb-aa18-50aefdbc4a70
-- title:
--   Verb: run Trace trace Of
-- statement:
--   **The emitted list is a consistent trace of the input** (`TraceOf`, `main.tex:1114–1118`).
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/TraceCertificate.lean#L84-L85
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/TraceCertificate.lean#L84-L85

module
public import Definitions.Def_LeanPool_PureNock_Trace
public import Definitions.Def_LeanPool_PureNock_TraceCertificate
set_option autoImplicit true
@[expose] public section
public section
open Nock
open Nock.Verb

theorem Nock.Verb.runTrace_traceOf {fuel : Nat} {v : Verb} {T : List Verb}
    (h : runTrace fuel v = some T) : TraceOf v T := by sorry
