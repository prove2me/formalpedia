-- Prove2me | Theorems.Thm_Nock_Verb_denP_F_subnode
-- name    : Nock.Verb.denP_F_subnode
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:15:08.950638+00:00
-- url     : https://prove2.me/theorems/653ce0d5-1847-44f1-bffe-dd4adc3d3651
-- title:
--   Verb: den P F subnode
-- statement:
--   The Verb construction uses the den P F subnode property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/PureComplete.lean#L921-L924
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/PureComplete.lean#L921-L924

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

theorem Nock.Verb.denP_F_subnode {F : Nat} {v : Verb} {x : Noun} (hok : editOk v = true)
    (hv : denP F v = some x) {i : Nat} {sub : Verb} (hmap : map i v = some sub) :
    ∃ y, denP F sub = some y := by sorry
