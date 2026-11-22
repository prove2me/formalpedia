-- Prove2me | Theorems.Thm_Nock_Verb_runTraceProgram_certificate
-- name    : Nock.Verb.runTraceProgram_certificate
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:29:53.28141+00:00
-- url     : https://prove2.me/theorems/8cf043ae-8e1c-4405-a74a-b6b8c8277228
-- title:
--   Verb: run Trace Program certificate
-- statement:
--   **`runTraceProgram` emits a certified trace of the program.**  Its head is the program verb,
--       it is consistent and complete, every adjacent step passes the checker `Nock`, and the final
--       state is terminal or has a crash edge accepted by the checker.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/TraceCertificate.lean#L225-L229
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/TraceCertificate.lean#L225-L229

module
public import Definitions.Def_LeanPool_PureNock_Trace
public import Definitions.Def_LeanPool_PureNock_TraceCertificate
set_option autoImplicit true
@[expose] public section
public section
open Nock
open Nock.Verb

theorem Nock.Verb.runTraceProgram_certificate {fuel : Nat} {subject formula : Noun} {T : List Verb}
    (h : runTraceProgram fuel subject formula = some T) :
    TraceOf (program subject formula) T ∧ Complete T ∧ AdjNockCheck T ∧
      (∃ w, T.getLast? = some w ∧ (isTerminal w = true ∨ NockCheck w none = true)) := by sorry
