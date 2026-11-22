-- Prove2me | Theorems.Thm_Nock_Verb_inDomain_star_of
-- name    : Nock.Verb.inDomain_star_of
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:08:36.083285+00:00
-- url     : https://prove2.me/theorems/6c92604a-cbe4-4c28-8f32-ad902d5de0f1
-- title:
--   Verb: in Domain star of
-- statement:
--   A `*`-redex with terminal children and a valid opcode head is in the transition domain.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/PureAgreement.lean#L1668-L1672
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/PureAgreement.lean#L1668-L1672

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

theorem Nock.Verb.inDomain_star_of {L I n2 : Verb} {rb : Action}
    (hL : isTerminal L = true) (hrb : rb.isNull = true) (hI : isTerminal I = true)
    (hn2 : isTerminal n2 = true) (hhead : opHeadOk I = true) :
    inDomain (Verb.node .star L (Verb.node rb I n2)) = true := by sorry
