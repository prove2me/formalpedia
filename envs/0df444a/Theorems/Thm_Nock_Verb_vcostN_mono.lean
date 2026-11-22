-- Prove2me | Theorems.Thm_Nock_Verb_vcostN_mono
-- name    : Nock.Verb.vcostN_mono
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:16:05.255946+00:00
-- url     : https://prove2.me/theorems/95078105-ad6e-4ccd-bce0-24a4f3c8906e
-- title:
--   Verb: vcost N mono
-- statement:
--   The Verb construction uses the vcost N mono property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/PureCompleteHint.lean#L424-L428
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/PureCompleteHint.lean#L424-L428

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

theorem Nock.Verb.vcostN_mono {F G : Nat} {v : Verb} {x : Noun}
    (hle : F ≤ G) (hok : editOk v = true) (hv : den F v = some x) : vcostN G v = vcostN F v := by sorry
