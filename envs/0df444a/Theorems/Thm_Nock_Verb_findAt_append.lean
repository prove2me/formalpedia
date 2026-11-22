-- Prove2me | Theorems.Thm_Nock_Verb_findAt_append
-- name    : Nock.Verb.findAt_append
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:01:01.255861+00:00
-- url     : https://prove2.me/theorems/f0106087-e4a0-44e9-89a1-37a67c774b1d
-- title:
--   Verb: find At append
-- statement:
--   `findAt` over an append: the left list wins if it has a match.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/Verb.lean#L365-L379
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/Verb.lean#L365-L379

module
public import Definitions.Def_LeanPool_PureNock_Tree
public import Definitions.Def_LeanPool_PureNock_Reference
public import Definitions.Def_LeanPool_PureNock_Verb
set_option autoImplicit true
@[expose] public section
public section
open Nock
open Nock.Verb

theorem Nock.Verb.findAt_append (i : Nat) :
    ∀ (L1 L2 : List (Nat × Verb)),
      findAt i (L1 ++ L2) = match findAt i L1 with
                            | some v => some v
                            | none   => findAt i L2
 := by sorry
