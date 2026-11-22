-- Prove2me | Theorems.Thm_Nock_Verb_DenP_ofNoun_iff
-- name    : Nock.Verb.DenP_ofNoun_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:13:55.577456+00:00
-- url     : https://prove2.me/theorems/2325f362-b859-4437-bfe7-c2511bedfd2d
-- title:
--   Verb: Den P of Noun iff
-- statement:
--   Paper-denotation analogue of `Den_ofNoun_iff` (helper).
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/PureAgreement.lean#L1011-L1012
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/PureAgreement.lean#L1011-L1012

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

theorem Nock.Verb.DenP_ofNoun_iff {n x} : DenP (ofNoun n) x ↔ x = n := by sorry
