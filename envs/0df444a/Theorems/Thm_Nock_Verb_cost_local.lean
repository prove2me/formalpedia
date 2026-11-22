-- Prove2me | Theorems.Thm_Nock_Verb_cost_local
-- name    : Nock.Verb.cost_local
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:15:02.144837+00:00
-- url     : https://prove2.me/theorems/dc50dd7a-837e-44fe-b43c-6896442f9e28
-- title:
--   Verb: cost local
-- statement:
--   The Verb construction uses the cost local property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/PureComplete.lean#L761-L903
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/PureComplete.lean#L761-L903

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

theorem Nock.Verb.cost_local {F : Nat} {L R rr : Verb} {x : Noun}
    (hL : isTerminal L = true) (hR : isTerminal R = true)
    (hv : denP F (Verb.node .star L R) = some x)
    (hr : reduce (Verb.node .star L R) = some rr) :
    vcost F rr < vcost F (Verb.node .star L R) := by sorry
