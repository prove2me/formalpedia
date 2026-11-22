-- Prove2me | Theorems.Thm_Nock_FieldEmbedding_zmod_natCast_inj_of_lt
-- name    : Nock.FieldEmbedding.zmod_natCast_inj_of_lt
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:18:01.382913+00:00
-- url     : https://prove2.me/theorems/e0d9d425-e5ab-43b7-bb01-aa3cdc9b3034
-- title:
--   Field Embedding: zmod nat Cast inj of lt
-- statement:
--   The `Nat` cast into `ZMod q` is injective on canonical representatives `[0,q)`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/ModularEval.lean#L741-L744
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/ModularEval.lean#L741-L744

module
public import Definitions.Def_LeanPool_PureNock_Reference
public import Mathlib.Data.ZMod.Basic
public import Definitions.Def_LeanPool_PureNock_ModularEval
set_option autoImplicit true
@[expose] public section
public section
open Nock Nock.FieldEmbedding
open Nock Nock.Noun

theorem Nock.FieldEmbedding.zmod_natCast_inj_of_lt {q m n : ℕ} (hm : m < q) (hn : n < q)
    (h : (m : ZMod q) = (n : ZMod q)) : m = n := by sorry
