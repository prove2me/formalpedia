-- Prove2me | Theorems.Thm_Nock_Verb_nextHint_eq_some_iff
-- name    : Nock.Verb.nextHint_eq_some_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:03:46.755489+00:00
-- url     : https://prove2.me/theorems/d86685e3-8c0e-4eb3-8564-a1b80a34a080
-- title:
--   Verb: next Hint eq some iff
-- statement:
--   `nextHint` realizes the strict DFS selection step over `inDomainHint`/`redexHint`
--       (OP₁₁ analogue of `next_eq_some_iff`).
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/PureAgreement.lean#L806-L830
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/PureAgreement.lean#L806-L830

module
public import Definitions.Def_LeanPool_PureNock_Agreement
public import Definitions.Def_LeanPool_PureNock_Trace
public import Definitions.Def_LeanPool_PureNock_PaperReference
public import Mathlib.Tactic.IntervalCases
public import Definitions.Def_LeanPool_PureNock_PureAgreement
set_option autoImplicit true
@[expose] public section
public section
open Nock
open Nock.Verb
open Noun

theorem Nock.Verb.nextHint_eq_some_iff {a b : Verb} : nextHint a = some b ↔
    ∃ i sub r, IsMaxPending dfsLt a i ∧ map i a = some sub ∧ inDomainHint sub = true
      ∧ redexHint sub = some r ∧ b = replaceAt i a r := by sorry
