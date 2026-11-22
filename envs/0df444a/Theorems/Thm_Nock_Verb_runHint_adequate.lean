-- Prove2me | Theorems.Thm_Nock_Verb_runHint_adequate
-- name    : Nock.Verb.runHint_adequate
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:14:06.489287+00:00
-- url     : https://prove2.me/theorems/ba88b81f-5526-42c9-a11b-0ca3928d95ba
-- title:
--   Verb: run Hint adequate
-- statement:
--   Conditional wrapper for OP₁₁ adequacy (see `runHint_adequate_complete`).
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/PureAgreement.lean#L1567-L1569
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/PureAgreement.lean#L1567-L1569

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

theorem Nock.Verb.runHint_adequate (hc : HintComplete) (s f r : Noun) :
    (∃ fuel, runHintProgram fuel s f = some r) ↔ (∃ fuel, evalN fuel s f = some r) := by sorry
