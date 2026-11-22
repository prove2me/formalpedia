-- Prove2me | Theorems.Thm_Nock_Verb_ofNoun_noun
-- name    : Nock.Verb.ofNoun_noun
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:07:11.012356+00:00
-- url     : https://prove2.me/theorems/e10ba138-b737-4f56-bf4e-23d9309a4cee
-- title:
--   Verb: of Noun noun
-- statement:
--   The Verb construction uses the of Noun noun property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/Agreement.lean#L547-L550
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/Agreement.lean#L547-L550

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

theorem Nock.Verb.ofNoun_noun (n : Noun) : (ofNoun n).noun = n := by sorry
