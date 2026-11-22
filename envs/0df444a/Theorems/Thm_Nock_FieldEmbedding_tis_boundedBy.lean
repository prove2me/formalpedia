-- Prove2me | Theorems.Thm_Nock_FieldEmbedding_tis_boundedBy
-- name    : Nock.FieldEmbedding.tis_boundedBy
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:09:35.49337+00:00
-- url     : https://prove2.me/theorems/f6c638b1-d4e2-4d4a-b79a-4809571ffc77
-- title:
--   Field Embedding: tis bounded By
-- statement:
--   The Field Embedding construction uses the tis bounded By property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/ModularEval.lean#L287-L291
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/ModularEval.lean#L287-L291

module
public import Definitions.Def_LeanPool_PureNock_Reference
public import Mathlib.Data.ZMod.Basic
public import Definitions.Def_LeanPool_PureNock_ModularEval
set_option autoImplicit true
@[expose] public section
public section
open Nock Nock.FieldEmbedding
open Nock Nock.Noun

theorem Nock.FieldEmbedding.tis_boundedBy {q : ℕ} (hq : 1 < q) (a b : Noun) : BoundedBy q (tis a b) := by sorry
