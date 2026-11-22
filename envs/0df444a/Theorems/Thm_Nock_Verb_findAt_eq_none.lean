-- Prove2me | Theorems.Thm_Nock_Verb_findAt_eq_none
-- name    : Nock.Verb.findAt_eq_none
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:02:51.291301+00:00
-- url     : https://prove2.me/theorems/ad37eab3-05fe-4c63-93ad-87c5e508687b
-- title:
--   Verb: find At eq none
-- statement:
--   If no pair in `L` carries index `i`, then `findAt i L = none`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/Verb.lean#L382-L388
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/Verb.lean#L382-L388

module
public import Definitions.Def_LeanPool_PureNock_Tree
public import Definitions.Def_LeanPool_PureNock_Reference
public import Definitions.Def_LeanPool_PureNock_Verb
set_option autoImplicit true
@[expose] public section
public section
open Nock
open Nock.Verb

theorem Nock.Verb.findAt_eq_none {i : Nat} :
    ∀ {L : List (Nat × Verb)}, (∀ p ∈ L, p.1 ≠ i) → findAt i L = none
  := by sorry
