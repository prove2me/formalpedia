-- Prove2me | Theorems.Thm_Nock_Verb_runTrace_final_edge
-- name    : Nock.Verb.runTrace_final_edge
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:18:31.759509+00:00
-- url     : https://prove2.me/theorems/bd26dcbf-0453-4f03-8a13-08dc64e49fc5
-- title:
--   Verb: run Trace final edge
-- statement:
--   **The completion edge is accounted for.**  The emitted trace's last verb is either terminal
--       (a *valid* completion, `main.tex:1123`) or crashes, and in the crash case the transition to `⊥`
--       passes the checker (`NockCheck w none = true`, `main.tex:1124`, `1644`, `1650`).  Together with
--       `runTrace_adjacent_nockCheck`, every edge of the certificate — including the final ⊥ edge on a
--       crash — is `Nock`-checked; there is no unchecked step.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/TraceCertificate.lean#L211-L220
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/TraceCertificate.lean#L211-L220

module
public import Definitions.Def_LeanPool_PureNock_Trace
public import Definitions.Def_LeanPool_PureNock_TraceCertificate
set_option autoImplicit true
@[expose] public section
public section
open Nock
open Nock.Verb

theorem Nock.Verb.runTrace_final_edge {fuel : Nat} {v : Verb} {T : List Verb}
    (h : runTrace fuel v = some T) :
    ∃ w, T.getLast? = some w ∧ (isTerminal w = true ∨ NockCheck w none = true) := by sorry
