-- Prove2me | Theorems.Thm_Nock_FieldEmbedding_slot_boundedBy
-- name    : Nock.FieldEmbedding.slot_boundedBy
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:06:07.307421+00:00
-- url     : https://prove2.me/theorems/3eecb117-e74d-4a92-a8ab-87390c97f334
-- title:
--   Field Embedding: slot bounded By
-- statement:
--   `slot` returns a subtree of `n`, so it preserves every numeric leaf bound.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/ModularEval.lean#L226-L246
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/ModularEval.lean#L226-L246

module
public import Definitions.Def_LeanPool_PureNock_Reference
public import Mathlib.Data.ZMod.Basic
public import Definitions.Def_LeanPool_PureNock_ModularEval
set_option autoImplicit true
@[expose] public section
public section
open Nock Nock.FieldEmbedding
open Nock Nock.Noun

theorem Nock.FieldEmbedding.slot_boundedBy (q : ℕ) (ax : Nat) (n : Noun) :
    BoundedBy q n → ∀ {m : Noun}, slot ax n = some m → BoundedBy q m := by sorry
