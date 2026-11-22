-- Prove2me | Theorems.Thm_Nock_Verb_slot_pair_some
-- name    : Nock.Verb.slot_pair_some
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:07:26.785224+00:00
-- url     : https://prove2.me/theorems/08b5e562-e112-45c6-b8ec-93d0a6f942fa
-- title:
--   Verb: slot pair some
-- statement:
--   On a pair of atoms `[p,q]`, only axes `1,2,3` are addressable.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/Agreement.lean#L593-L614
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/Agreement.lean#L593-L614

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

theorem Nock.Verb.slot_pair_some {p q : Nat} : ∀ (m : Nat) (v : Noun),
    Noun.slot m (.cell (.atom p) (.atom q)) = some v → m = 1 ∨ m = 2 ∨ m = 3 := by sorry
