-- Prove2me | Theorems.Thm_Nock_Verb_ofNoun_terminal
-- name    : Nock.Verb.ofNoun_terminal
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:01:52.837459+00:00
-- url     : https://prove2.me/theorems/130370e4-c9cb-4774-99be-28e3ad9b611f
-- title:
--   Verb: of Noun terminal
-- statement:
--   The Verb construction uses the of Noun terminal property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/Agreement.lean#L552-L555
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/Agreement.lean#L552-L555

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

theorem Nock.Verb.ofNoun_terminal (n : Noun) : isTerminal (ofNoun n) = true := by sorry
