-- Prove2me | Theorems.Thm_Nock_Verb_domain
-- name    : Nock.Verb.domain
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:10:26.886786+00:00
-- url     : https://prove2.me/theorems/dd6fb31d-5642-4a25-a0dd-2689540239d8
-- title:
--   Verb: domain
-- statement:
--   **`Lem:domain`** (`main.tex:1141–1142`).
--       Let `c` be a continuation not followed by a null operator in a consistent evaluation
--       trace. Then `map(c, getIndex(c)) ∈ D(V)`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/Trace.lean#L123-L135
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/Trace.lean#L123-L135

module
public import Definitions.Def_LeanPool_PureNock_Verb
public import Batteries.Tactic.Alias
public import Definitions.Def_LeanPool_PureNock_Trace
set_option autoImplicit true
@[expose] public section
public section
open Nock
open Nock.Verb

theorem Nock.Verb.domain {c t : Verb} (h : Step c t) :
    ∃ i sub, getIndex c = some i ∧ map i c = some sub ∧ inDomain sub = true := by sorry
