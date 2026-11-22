-- Prove2me | Theorems.Thm_Nock_Verb_reduce_none_of_isHintRedex
-- name    : Nock.Verb.reduce_none_of_isHintRedex
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:13:30.210276+00:00
-- url     : https://prove2.me/theorems/8ed273a7-3578-46a3-8b63-b6d0e8eccd1f
-- title:
--   Verb: reduce none of is Hint Redex
-- statement:
--   **A hint redex is not a paper redex: `reduce` crashes on it.**  An OP₁₁ head fails
--       `opHeadOk` (`op < 11`), so the paper local rewrite `redex`/`reduce` returns `⊥`.  This is
--       what forces the extended domain to be `inDomain ∨ isHintRedex`, disjointly.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/PureAgreement.lean#L623-L628
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/PureAgreement.lean#L623-L628

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

theorem Nock.Verb.reduce_none_of_isHintRedex {sub} (h : isHintRedex sub = true) : reduce sub = none := by sorry
