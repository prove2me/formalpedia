-- Prove2me | Theorems.Thm_Nock_Verb_enum_denP_defined
-- name    : Nock.Verb.enum_denP_defined
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:14:12.852065+00:00
-- url     : https://prove2.me/theorems/70a3c479-53fb-4545-9fc3-9c302f984a2c
-- title:
--   Verb: enum den P defined
-- statement:
--   **`denP`-definedness descends to every enumerated subnode** (given `editOk`).
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/PureAgreement.lean#L1623-L1643
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/PureAgreement.lean#L1623-L1643

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

theorem Nock.Verb.enum_denP_defined :
    ∀ (v : Verb), editOk v = true → ∀ (c f : Nat) (x : Noun),
      denP f v = some x → ∀ p ∈ (enum v c).2, ∃ g y, denP g p.2 = some y := by sorry
