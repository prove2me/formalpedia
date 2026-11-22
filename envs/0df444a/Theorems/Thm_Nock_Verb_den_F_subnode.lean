-- Prove2me | Theorems.Thm_Nock_Verb_den_F_subnode
-- name    : Nock.Verb.den_F_subnode
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:16:15.105845+00:00
-- url     : https://prove2.me/theorems/3307c555-8e11-4ea6-8dde-d1d30a375294
-- title:
--   Verb: den F subnode
-- statement:
--   The Verb construction uses the den F subnode property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/PureCompleteHint.lean#L1247-L1250
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/PureCompleteHint.lean#L1247-L1250

module
public import Definitions.Def_LeanPool_PureNock_PureComplete
public import Mathlib.Tactic.IntervalCases
public import Definitions.Def_LeanPool_PureNock_PureCompleteHint
set_option autoImplicit true
@[expose] public section
public section
open Nock
open Nock.Verb
open Noun

theorem Nock.Verb.den_F_subnode {F : Nat} {v : Verb} {x : Noun} (hok : editOk v = true)
    (hv : den F v = some x) {i : Nat} {sub : Verb} (hmap : map i v = some sub) :
    ∃ y, den F sub = some y := by sorry
