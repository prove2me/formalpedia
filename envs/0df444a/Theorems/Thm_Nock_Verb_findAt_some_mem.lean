-- Prove2me | Theorems.Thm_Nock_Verb_findAt_some_mem
-- name    : Nock.Verb.findAt_some_mem
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:01:49.035799+00:00
-- url     : https://prove2.me/theorems/349e45fa-3850-4ad6-bac3-8f70c154ca40
-- title:
--   Verb: find At some mem
-- statement:
--   `findAt i L = some v` witnesses membership `(i, v) ∈ L`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/Verb.lean#L391-L401
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/Verb.lean#L391-L401

module
public import Definitions.Def_LeanPool_PureNock_Tree
public import Definitions.Def_LeanPool_PureNock_Reference
public import Definitions.Def_LeanPool_PureNock_Verb
set_option autoImplicit true
@[expose] public section
public section
open Nock
open Nock.Verb

theorem Nock.Verb.findAt_some_mem {i : Nat} {v : Verb} :
    ∀ {L : List (Nat × Verb)}, findAt i L = some v → (i, v) ∈ L
  := by sorry
