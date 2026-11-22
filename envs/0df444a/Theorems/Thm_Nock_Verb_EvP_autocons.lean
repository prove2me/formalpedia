-- Prove2me | Theorems.Thm_Nock_Verb_EvP_autocons
-- name    : Nock.Verb.EvP_autocons
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:12:40.399485+00:00
-- url     : https://prove2.me/theorems/87b50fa8-36f4-400d-8eb7-9d7df3aa34fe
-- title:
--   Verb: Ev P autocons
-- statement:
--   The Verb construction uses the Ev P autocons property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/PureAgreement.lean#L178-L192
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/PureAgreement.lean#L178-L192

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

theorem Nock.Verb.EvP_autocons {subj hb hc d x} : EvP subj (.cell (.cell hb hc) d) x ↔
    ∃ l r, x = .cell l r ∧ EvP subj (.cell hb hc) l ∧ EvP subj d r := by sorry
