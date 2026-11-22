-- Prove2me | Theorems.Thm_Nock_Verb_cost_localN
-- name    : Nock.Verb.cost_localN
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:16:10.140238+00:00
-- url     : https://prove2.me/theorems/cd3700fb-4d4a-488f-ba1a-d71df86deeba
-- title:
--   Verb: cost local N
-- statement:
--   The Verb construction uses the cost local N property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/PureCompleteHint.lean#L1081-L1229
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/PureCompleteHint.lean#L1081-L1229

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

theorem Nock.Verb.cost_localN {F : Nat} {L R rr : Verb} {x : Noun}
    (hL : isTerminal L = true) (hR : isTerminal R = true)
    (hv : den F (Verb.node .star L R) = some x)
    (hr : redexHint (Verb.node .star L R) = some rr) :
    vcostN F rr < vcostN F (Verb.node .star L R) := by sorry
