-- Prove2me | Theorems.Thm_Nock_Verb_den_det
-- name    : Nock.Verb.den_det
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:07:11.274245+00:00
-- url     : https://prove2.me/theorems/fdd46797-e68a-4a2a-a458-68f5e5991c92
-- title:
--   Verb: den det
-- statement:
--   The Verb construction uses the den det property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/Agreement.lean#L536-L540
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/Agreement.lean#L536-L540

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

theorem Nock.Verb.den_det {v r1 r2} (h1 : Den v r1) (h2 : Den v r2) : r1 = r2 := by sorry
