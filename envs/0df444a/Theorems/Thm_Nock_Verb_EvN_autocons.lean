-- Prove2me | Theorems.Thm_Nock_Verb_EvN_autocons
-- name    : Nock.Verb.EvN_autocons
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:11:26.712811+00:00
-- url     : https://prove2.me/theorems/e5410275-4928-4254-9fd1-6dd6a17bf9f6
-- title:
--   Verb: Ev N autocons
-- statement:
--   The Verb construction uses the Ev N autocons property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/Agreement.lean#L303-L317
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/Agreement.lean#L303-L317

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

theorem Nock.Verb.EvN_autocons {subj hb hc d x} : Ev subj (.cell (.cell hb hc) d) x ↔
    ∃ l r, x = .cell l r ∧ Ev subj (.cell hb hc) l ∧ Ev subj d r := by sorry
