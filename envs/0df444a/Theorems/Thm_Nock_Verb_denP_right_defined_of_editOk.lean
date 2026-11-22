-- Prove2me | Theorems.Thm_Nock_Verb_denP_right_defined_of_editOk
-- name    : Nock.Verb.denP_right_defined_of_editOk
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:14:11.996535+00:00
-- url     : https://prove2.me/theorems/b85b4b65-62b7-48b0-9c68-8787adb4a1b3
-- title:
--   Verb: den P right defined of edit Ok
-- statement:
--   `denP` of an `editOk` node forces the RIGHT child to be `denP`-defined (the `edit` case uses
--       `editOk`: its right child is non-pending, hence a `⊥`-cons of its two `denP`-defined args).
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/PureAgreement.lean#L1590-L1620
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/PureAgreement.lean#L1590-L1620

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

theorem Nock.Verb.denP_right_defined_of_editOk {a : Action} {l r : Verb} {f : Nat} {x : Noun}
    (hok : editOk (Verb.node a l r) = true) (h : denP (f + 1) (Verb.node a l r) = some x) :
    ∃ g y, denP g r = some y := by sorry
