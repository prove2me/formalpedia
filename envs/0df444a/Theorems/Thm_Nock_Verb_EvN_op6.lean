-- Prove2me | Theorems.Thm_Nock_Verb_EvN_op6
-- name    : Nock.Verb.EvN_op6
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:07:11.524207+00:00
-- url     : https://prove2.me/theorems/709d1a42-be02-45b8-b589-c1d323481b19
-- title:
--   Verb: Ev N op6
-- statement:
--   The Verb construction uses the Ev N op6 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/Agreement.lean#L467-L501
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/Agreement.lean#L467-L501

module
public import Definitions.Def_LeanPool_PureNock_Verb
public import Definitions.Def_LeanPool_PureNock_Semantics
public import Definitions.Def_LeanPool_PureNock_Agreement
set_option autoImplicit true
@[expose] public section
public section
open Nock
open Nock.Verb
open Noun

theorem Nock.Verb.EvN_op6 {subj tail x} : Ev subj (.cell (.atom 6) tail) x ↔
    ∃ b c d cv, tail = .cell b (.cell c d) ∧ Ev subj b cv ∧
      ((cv = .atom 0 ∧ Ev subj c x) ∨ (cv = .atom 1 ∧ Ev subj d x)) := by sorry
