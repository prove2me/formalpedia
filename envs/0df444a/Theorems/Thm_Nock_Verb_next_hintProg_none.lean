-- Prove2me | Theorems.Thm_Nock_Verb_next_hintProg_none
-- name    : Nock.Verb.next_hintProg_none
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:08:11.719152+00:00
-- url     : https://prove2.me/theorems/b299eec3-8e4a-49f5-a7f5-981e0435ce31
-- title:
--   Verb: next hint Prog none
-- statement:
--   The paper machine crashes at the root OP₁₁ redex of a hint program: `next` of the
--       program verb is `⊥`, because an OP₁₁ head is out of the paper domain (`opHeadOk`,
--       `op < 11`) and the root `*`-node carries no operator.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/PureAgreement.lean#L926-L942
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/PureAgreement.lean#L926-L942

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

theorem Nock.Verb.next_hintProg_none (subj n2 : Noun) :
    next (program subj (.cell (.atom 11) n2)) = none := by sorry
