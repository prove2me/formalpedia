-- Prove2me | Theorems.Thm_Nock_Verb_denP_terminal
-- name    : Nock.Verb.denP_terminal
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:07:31.226496+00:00
-- url     : https://prove2.me/theorems/b90121b9-ad92-467b-8877-dcab62f2f868
-- title:
--   Verb: den P terminal
-- statement:
--   `denP` of any terminal verb is its underlying noun (given adequate fuel).  Identical to
--       `den_terminal`: a terminal verb has no `*`-node, so `evalPaper`/`evalN` never enter.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/PureAgreement.lean#L86-L101
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/PureAgreement.lean#L86-L101

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

theorem Nock.Verb.denP_terminal : ∀ (v : Verb) (fuel : Nat),
    isTerminal v = true → v.noun.size ≤ fuel → denP fuel v = some v.noun := by sorry
