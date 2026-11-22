-- Prove2me | Theorems.Thm_Nock_Verb_den_iff_evalN
-- name    : Nock.Verb.den_iff_evalN
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:04:19.288136+00:00
-- url     : https://prove2.me/theorems/7b7947ad-0a0d-4bfc-a6c2-c8164a82d842
-- title:
--   Verb: den iff eval N
-- statement:
--   `den` of `*[s, f]` and `evalN s f` define the same partial function.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/Agreement.lean#L127-L143
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/Agreement.lean#L127-L143

module
public import Definitions.Def_LeanPool_PureNock_Verb
public import Definitions.Def_LeanPool_PureNock_Semantics
public import Definitions.Def_LeanPool_PureNock_Agreement
set_option autoImplicit true
@[expose] public section
public section
open Nock
open Nock.Verb
open Noun

theorem Nock.Verb.den_iff_evalN (s f r : Noun) :
    (∃ fuel, den fuel (program s f) = some r) ↔ (∃ fuel, evalN fuel s f = some r) := by sorry
