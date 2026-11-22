-- Prove2me | Theorems.Thm_Nock_Verb_denP_star_val
-- name    : Nock.Verb.denP_star_val
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:14:41.14427+00:00
-- url     : https://prove2.me/theorems/78c88a7a-4073-4e39-a537-00bfb97e9235
-- title:
--   Verb: den P star val
-- statement:
--   The Verb construction uses the den P star val property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/PureComplete.lean#L102-L105
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/PureComplete.lean#L102-L105

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

theorem Nock.Verb.denP_star_val {A B : Verb} {f : Nat} {a b w : Noun}
    (hA : denP f A = some a) (hB : denP f B = some b) (he : evalPaper f a b = some w) :
    denP (f + 1) (Verb.node .star A B) = some w := by sorry
