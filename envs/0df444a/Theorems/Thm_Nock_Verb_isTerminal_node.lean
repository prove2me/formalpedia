-- Prove2me | Theorems.Thm_Nock_Verb_isTerminal_node
-- name    : Nock.Verb.isTerminal_node
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:08:38.528838+00:00
-- url     : https://prove2.me/theorems/2890fa34-46c1-44ed-b3e7-0d1eea86e20f
-- title:
--   Verb: is Terminal node
-- statement:
--   The Verb construction uses the is Terminal node property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/PureComplete.lean#L71-L72
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/PureComplete.lean#L71-L72

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

theorem Nock.Verb.isTerminal_node {a : Action} {l r : Verb} :
    isTerminal (Verb.node a l r) = (a.isNull && isTerminal l && isTerminal r) := by sorry
