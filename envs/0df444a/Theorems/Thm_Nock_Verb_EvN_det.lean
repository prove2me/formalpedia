-- Prove2me | Theorems.Thm_Nock_Verb_EvN_det
-- name    : Nock.Verb.EvN_det
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:15:31.944511+00:00
-- url     : https://prove2.me/theorems/ce1762a6-254d-4d84-84fe-452f7cd8c76b
-- title:
--   Verb: Ev N det
-- statement:
--   The Verb construction uses the Ev N det property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/PureCompleteHint.lean#L53-L56
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/PureCompleteHint.lean#L53-L56

module
public import Definitions.Def_LeanPool_PureNock_PureComplete
public import Mathlib.Tactic.IntervalCases
public import Definitions.Def_LeanPool_PureNock_PureCompleteHint
set_option autoImplicit true
@[expose] public section
public section
open Nock
open Nock.Verb
open Noun

theorem Nock.Verb.EvN_det {a b y1 y2 : Noun} (h1 : Ev a b y1) (h2 : Ev a b y2) : y1 = y2 := by sorry
