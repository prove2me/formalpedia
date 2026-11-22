-- Prove2me | Theorems.Thm_Nock_Verb_pcost_succ
-- name    : Nock.Verb.pcost_succ
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:08:37.674252+00:00
-- url     : https://prove2.me/theorems/68e9a54c-0941-42c9-a6c4-93a1c88c1676
-- title:
--   Verb: pcost succ
-- statement:
--   `pcost` is unchanged by extra fuel once `evalPaper` succeeds (mirrors `evalPaper_succ`).
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/PureAgreement.lean#L1909-L1914
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/PureAgreement.lean#L1909-L1914

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

theorem Nock.Verb.pcost_succ {n : Nat} {a b : Noun} {r : Noun}
    (hb : evalPaper n a b = some r) : pcost (n + 1) a b = pcost n a b := by sorry
