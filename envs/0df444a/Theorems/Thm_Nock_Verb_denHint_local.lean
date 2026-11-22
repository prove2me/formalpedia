-- Prove2me | Theorems.Thm_Nock_Verb_denHint_local
-- name    : Nock.Verb.denHint_local
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:08:12.387803+00:00
-- url     : https://prove2.me/theorems/60357f37-c3f3-4501-9c2f-a57c7f361745
-- title:
--   Verb: den Hint local
-- statement:
--   `redexHint` (hint expand, else `reduce`) preserves `den`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/PureAgreement.lean#L775-L790
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/PureAgreement.lean#L775-L790

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

theorem Nock.Verb.denHint_local {sub r₀ x} (hd : inDomainHint sub = true) (hr : redexHint sub = some r₀) :
    (Den sub x ↔ Den r₀ x) := by sorry
