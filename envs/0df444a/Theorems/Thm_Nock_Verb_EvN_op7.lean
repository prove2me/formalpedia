-- Prove2me | Theorems.Thm_Nock_Verb_EvN_op7
-- name    : Nock.Verb.EvN_op7
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:04:29.106891+00:00
-- url     : https://prove2.me/theorems/f4e739db-74da-4e1b-86e1-d088a62e4e4d
-- title:
--   Verb: Ev N op7
-- statement:
--   The Verb construction uses the Ev N op7 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/Agreement.lean#L407-L424
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/Agreement.lean#L407-L424

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

theorem Nock.Verb.EvN_op7 {subj tail x} : Ev subj (.cell (.atom 7) tail) x ↔
    ∃ hb hc sb, tail = .cell hb hc ∧ Ev subj hb sb ∧ Ev sb hc x := by sorry
