-- Prove2me | Theorems.Thm_Nock_Verb_DenP_subnode
-- name    : Nock.Verb.DenP_subnode
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:14:17.674687+00:00
-- url     : https://prove2.me/theorems/a0699747-628e-4c37-82f0-f114186b7a2a
-- title:
--   Verb: Den P subnode
-- statement:
--   The subnode `map i v = some sub` of a `denP`-defined `editOk` verb is itself `denP`-defined.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/PureAgreement.lean#L1646-L1651
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/PureAgreement.lean#L1646-L1651

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

theorem Nock.Verb.DenP_subnode {v : Verb} {x : Noun} (hok : editOk v = true) (hv : DenP v x)
    {i : Nat} {sub : Verb} (hmap : map i v = some sub) : ∃ y, DenP sub y := by sorry
