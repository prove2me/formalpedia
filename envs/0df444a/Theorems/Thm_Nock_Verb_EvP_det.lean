-- Prove2me | Theorems.Thm_Nock_Verb_EvP_det
-- name    : Nock.Verb.EvP_det
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:14:53.79169+00:00
-- url     : https://prove2.me/theorems/33069e3a-d723-4dd1-8e53-e40b7b52bafe
-- title:
--   Verb: Ev P det
-- statement:
--   The Verb construction uses the Ev P det property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/PureComplete.lean#L201-L204
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/PureComplete.lean#L201-L204

module
public import Definitions.Def_LeanPool_PureNock_PureAgreement
public import Mathlib.Tactic.IntervalCases
public import Definitions.Def_LeanPool_PureNock_PureComplete
set_option autoImplicit true
@[expose] public section
public section
open Nock
open Nock.Verb
open Noun

theorem Nock.Verb.EvP_det {a b y1 y2 : Noun} (h1 : EvP a b y1) (h2 : EvP a b y2) : y1 = y2 := by sorry
