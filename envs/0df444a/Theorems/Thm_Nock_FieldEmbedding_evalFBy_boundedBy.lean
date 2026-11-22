-- Prove2me | Theorems.Thm_Nock_FieldEmbedding_evalFBy_boundedBy
-- name    : Nock.FieldEmbedding.evalFBy_boundedBy
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:18:00.013135+00:00
-- url     : https://prove2.me/theorems/f728ede7-f978-4221-9336-c68661ccc996
-- title:
--   Field Embedding: eval FBy bounded By
-- statement:
--   The Field Embedding construction uses the eval FBy bounded By property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/ModularEval.lean#L577-L732
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/ModularEval.lean#L577-L732

module
public import Definitions.Def_LeanPool_PureNock_Reference
public import Mathlib.Data.ZMod.Basic
public import Definitions.Def_LeanPool_PureNock_ModularEval
set_option autoImplicit true
@[expose] public section
public section
open Nock Nock.FieldEmbedding
open Nock Nock.Noun

theorem Nock.FieldEmbedding.evalFBy_boundedBy {q : ℕ} (hq : 1 < q) :
    ∀ (fuel : Nat) (s f r : Noun), BoundedBy q s → BoundedBy q f →
      evalFBy q fuel s f = some r → BoundedBy q r := by sorry
