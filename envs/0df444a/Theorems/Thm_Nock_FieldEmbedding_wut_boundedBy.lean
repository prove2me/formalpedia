-- Prove2me | Theorems.Thm_Nock_FieldEmbedding_wut_boundedBy
-- name    : Nock.FieldEmbedding.wut_boundedBy
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:09:36.072619+00:00
-- url     : https://prove2.me/theorems/d3cefe85-95ce-4959-accb-898196002c51
-- title:
--   Field Embedding: wut bounded By
-- statement:
--   The Field Embedding construction uses the wut bounded By property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/ModularEval.lean#L280-L285
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/ModularEval.lean#L280-L285

module
public import Definitions.Def_LeanPool_PureNock_Reference
public import Mathlib.Data.ZMod.Basic
public import Definitions.Def_LeanPool_PureNock_ModularEval
set_option autoImplicit true
@[expose] public section
public section
open Nock Nock.FieldEmbedding
open Nock Nock.Noun

theorem Nock.FieldEmbedding.wut_boundedBy {q : ℕ} (hq : 1 < q) (x : Noun) : BoundedBy q (wut x) := by sorry
