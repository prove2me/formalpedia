-- Prove2me | Theorems.Thm_Nock_Verb_cost_stepP
-- name    : Nock.Verb.cost_stepP
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:15:18.512101+00:00
-- url     : https://prove2.me/theorems/034f8532-26af-4e55-afbb-057cfc1e024b
-- title:
--   Verb: cost step P
-- statement:
--   **A single machine step strictly decreases `vcost`** (at a common fuel `F`).
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/PureComplete.lean#L1040-L1104
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/PureComplete.lean#L1040-L1104

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

theorem Nock.Verb.cost_stepP {F : Nat} {v v' : Verb} {x x' : Noun}
    (hwf : editOk v = true) (hv : denP F v = some x) (hv' : denP F v' = some x')
    (h : next v = some v') : vcost F v' < vcost F v := by sorry
