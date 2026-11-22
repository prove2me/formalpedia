-- Prove2me | Theorems.Thm_Nock_Verb_slot_ge_two
-- name    : Nock.Verb.slot_ge_two
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:12:22.93385+00:00
-- url     : https://prove2.me/theorems/24780d2b-a29b-4b10-80f3-964b6bf7582b
-- title:
--   Verb: slot ge two
-- statement:
--   `slot` at any axis `≥ 2` in terms of the parent read `slot (m/2)` and the parity pick —
--       the `slot` equation stated for a general `m` rather than the `a+2` constructor pattern.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/Agreement.lean#L1518-L1525
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/Agreement.lean#L1518-L1525

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

theorem Nock.Verb.slot_ge_two (m : Nat) (hm : 2 ≤ m) (n : Noun) :
    Noun.slot m n
      = (match Noun.slot (m / 2) n with
         | some (.cell l r) => some (if m % 2 == 0 then l else r)
         | _ => none) := by sorry
