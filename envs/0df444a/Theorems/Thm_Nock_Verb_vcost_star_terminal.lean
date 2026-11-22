-- Prove2me | Theorems.Thm_Nock_Verb_vcost_star_terminal
-- name    : Nock.Verb.vcost_star_terminal
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:14:50.800629+00:00
-- url     : https://prove2.me/theorems/165c40d2-4de1-4754-9d91-ca32bcba5948
-- title:
--   Verb: vcost star terminal
-- statement:
--   `vcost` of a `*`-node with terminal, denP-defined children is the firing `pcost`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/PureComplete.lean#L145-L149
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/PureComplete.lean#L145-L149

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

theorem Nock.Verb.vcost_star_terminal {F : Nat} {A B : Verb}
    (hA : isTerminal A = true) (hB : isTerminal B = true)
    (hdA : denP F A = some A.noun) (hdB : denP F B = some B.noun) :
    vcost F (Verb.node .star A B) = pcost F A.noun B.noun := by sorry
