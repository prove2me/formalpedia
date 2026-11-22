-- Prove2me | Theorems.Thm_Nock_FieldEmbedding_BoundedBy_cell
-- name    : Nock.FieldEmbedding.BoundedBy_cell
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T11:59:50.295217+00:00
-- url     : https://prove2.me/theorems/e6589002-2b0b-40e9-9d5f-cfcf45285901
-- title:
--   Field Embedding: Bounded By cell
-- statement:
--   The Field Embedding construction uses the Bounded By cell property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/ModularEval.lean#L52-L53
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/ModularEval.lean#L52-L53

module
public import Definitions.Def_LeanPool_PureNock_Reference
public import Mathlib.Data.ZMod.Basic
public import Definitions.Def_LeanPool_PureNock_ModularEval
set_option autoImplicit true
@[expose] public section
public section
open Nock Nock.FieldEmbedding
open Nock Nock.Noun

theorem Nock.FieldEmbedding.BoundedBy_cell {q : ℕ} {l r : Noun} :
    BoundedBy q (.cell l r) ↔ BoundedBy q l ∧ BoundedBy q r := by sorry
