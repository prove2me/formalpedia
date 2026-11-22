-- Prove2me | Theorems.Thm_Nock_transcript_length
-- name    : Nock.transcript_length
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:09:22.172591+00:00
-- url     : https://prove2.me/theorems/7626fcb4-adc1-4a92-8011-aa78a31fd90e
-- title:
--   Nock: transcript length
-- statement:
--   The Nock construction uses the transcript length property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/NounValidation.lean#L197-L202
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/NounValidation.lean#L197-L202

module
public import Definitions.Def_LeanPool_PureNock_Tree
public import Mathlib.Data.Multiset.Basic
public import Mathlib.Data.Multiset.AddSub
public import Mathlib.Data.Multiset.MapFold
public import Mathlib.Algebra.BigOperators.Group.Multiset.Basic
public import Mathlib.Algebra.Ring.Nat
public import Definitions.Def_LeanPool_PureNock_NounValidation
set_option autoImplicit true
@[expose] public section
public section
open Nock

theorem Nock.transcript_length (n : Noun) : (transcript n).length = n.size := by sorry
