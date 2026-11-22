-- Prove2me | Theorems.Thm_Nock_Verb_adjNockCheckB_iff
-- name    : Nock.Verb.adjNockCheckB_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:18:31.218424+00:00
-- url     : https://prove2.me/theorems/d55cf03b-84f2-4492-85f5-9cc7747b9faa
-- title:
--   Verb: adj Nock Check B iff
-- statement:
--   `adjNockCheckB` decides `AdjNockCheck`: the executable checker returns `true` iff every
--       adjacent pair passes the paper's transition checker `Nock`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/TraceCertificate.lean#L119-L124
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/TraceCertificate.lean#L119-L124

module
public import Definitions.Def_LeanPool_PureNock_Trace
public import Definitions.Def_LeanPool_PureNock_TraceCertificate
set_option autoImplicit true
@[expose] public section
public section
open Nock
open Nock.Verb

theorem Nock.Verb.adjNockCheckB_iff : ∀ (T : List Verb), adjNockCheckB T = true ↔ AdjNockCheck T
  := by sorry
