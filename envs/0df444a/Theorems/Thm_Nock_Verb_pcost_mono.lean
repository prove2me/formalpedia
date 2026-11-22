-- Prove2me | Theorems.Thm_Nock_Verb_pcost_mono
-- name    : Nock.Verb.pcost_mono
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:14:25.389705+00:00
-- url     : https://prove2.me/theorems/65f4a40c-f667-468b-9ab5-9999c671668b
-- title:
--   Verb: pcost mono
-- statement:
--   `pcost` stabilizes for any fuel `≥ n` once `evalPaper n` succeeds.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/PureAgreement.lean#L1917-L1921
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/PureAgreement.lean#L1917-L1921

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

theorem Nock.Verb.pcost_mono {n m : Nat} {a b r : Noun} (hle : n ≤ m) (hb : evalPaper n a b = some r) :
    pcost m a b = pcost n a b := by sorry
