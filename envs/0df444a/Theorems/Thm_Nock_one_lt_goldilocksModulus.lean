-- Prove2me | Theorems.Thm_Nock_one_lt_goldilocksModulus
-- name    : Nock.one_lt_goldilocksModulus
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:18:23.984554+00:00
-- url     : https://prove2.me/theorems/d780e02c-2469-4686-819b-a85e5d05a865
-- title:
--   Nock: one lt goldilocks Modulus
-- statement:
--   The Nock construction uses the one lt goldilocks Modulus property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/PaperFieldBridge.lean#L305-L306
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/PaperFieldBridge.lean#L305-L306

module
public import Definitions.Def_LeanPool_PureNock_PaperReferenceMod
public import Definitions.Def_LeanPool_PureNock_PureComplete
public import Definitions.Def_LeanPool_PureNock_PaperFieldBridge
set_option autoImplicit true
@[expose] public section
public section
open Nock
open Noun

theorem Nock.one_lt_goldilocksModulus : 1 < goldilocksModulus := by sorry
