-- Prove2me | Theorems.Thm_Nock_FieldEmbedding_agreeBy
-- name    : Nock.FieldEmbedding.agreeBy
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:06:10.485741+00:00
-- url     : https://prove2.me/theorems/ca0b9e0b-61ca-4053-8814-6b7d1ae9080f
-- title:
--   Field Embedding: agree By
-- statement:
--   The Field Embedding construction uses the agree By property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/ModularEval.lean#L369-L553
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/ModularEval.lean#L369-L553

module
public import Definitions.Def_LeanPool_PureNock_Reference
public import Mathlib.Data.ZMod.Basic
public import Definitions.Def_LeanPool_PureNock_ModularEval
set_option autoImplicit true
@[expose] public section
public section
open Nock Nock.FieldEmbedding
open Nock Nock.Noun

theorem Nock.FieldEmbedding.agreeBy (q : ℕ) (hq : 1 < q) :
    ∀ (fuel : Nat) (s f r : Noun), BoundedBy q s → BoundedBy q f →
      evalGBy q fuel s f = some r →
        evalN fuel s f = some r ∧ evalFBy q fuel s f = some r ∧ BoundedBy q r := by sorry
