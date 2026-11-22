-- Prove2me | Theorems.Thm_Nock_Verb_vcostN_star_terminal
-- name    : Nock.Verb.vcostN_star_terminal
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:16:01.337625+00:00
-- url     : https://prove2.me/theorems/570f431e-186d-498e-9582-4484cd631273
-- title:
--   Verb: vcost N star terminal
-- statement:
--   The Verb construction uses the vcost N star terminal property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/PureCompleteHint.lean#L381-L385
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/PureCompleteHint.lean#L381-L385

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

theorem Nock.Verb.vcostN_star_terminal {F : Nat} {A B : Verb}
    (hA : isTerminal A = true) (hB : isTerminal B = true)
    (hdA : den F A = some A.noun) (hdB : den F B = some B.noun) :
    vcostN F (Verb.node .star A B) = ncost F A.noun B.noun := by sorry
