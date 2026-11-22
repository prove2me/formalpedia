-- Prove2me | Theorems.Thm_Nock_Verb_denP_ofNoun
-- name    : Nock.Verb.denP_ofNoun
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:12:34.542034+00:00
-- url     : https://prove2.me/theorems/9456c3b7-50cd-4b63-8534-e5cb486ab1ef
-- title:
--   Verb: den P of Noun
-- statement:
--   `denP` of the terminal verb `ofNoun n` is `n` (given adequate fuel; cf. `den_ofNoun`).
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/PureAgreement.lean#L104-L114
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/PureAgreement.lean#L104-L114

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

theorem Nock.Verb.denP_ofNoun : ∀ (n : Noun) (fuel : Nat), n.size ≤ fuel → denP fuel (ofNoun n) = some n := by sorry
