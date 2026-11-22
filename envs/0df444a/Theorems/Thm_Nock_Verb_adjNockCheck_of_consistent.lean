-- Prove2me | Theorems.Thm_Nock_Verb_adjNockCheck_of_consistent
-- name    : Nock.Verb.adjNockCheck_of_consistent
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:18:29.50628+00:00
-- url     : https://prove2.me/theorems/832cca79-f847-4b1c-a978-ce4382fc016a
-- title:
--   Verb: adj Nock Check of consistent
-- statement:
--   A consistent trace is accepted pairwise by the transition checker: every `Step a b`
--       (`next a = some b`) makes `NockCheck a (some b) = true` (`nockCheck_eq_true_iff`).
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/TraceCertificate.lean#L102-L108
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/TraceCertificate.lean#L102-L108

module
public import Definitions.Def_LeanPool_PureNock_Trace
public import Definitions.Def_LeanPool_PureNock_TraceCertificate
set_option autoImplicit true
@[expose] public section
public section
open Nock
open Nock.Verb

theorem Nock.Verb.adjNockCheck_of_consistent : ∀ (T : List Verb), Consistent T → AdjNockCheck T
  := by sorry
