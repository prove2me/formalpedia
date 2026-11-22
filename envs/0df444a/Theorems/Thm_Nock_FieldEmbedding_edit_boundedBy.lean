-- Prove2me | Theorems.Thm_Nock_FieldEmbedding_edit_boundedBy
-- name    : Nock.FieldEmbedding.edit_boundedBy
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:09:34.434649+00:00
-- url     : https://prove2.me/theorems/5c171e34-cd45-47aa-9d28-c7fec8da3635
-- title:
--   Field Embedding: edit bounded By
-- statement:
--   `edit` grafts `new` into `old`, so it preserves every numeric leaf bound.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/ModularEval.lean#L249-L271
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/ModularEval.lean#L249-L271

module
public import Definitions.Def_LeanPool_PureNock_Reference
public import Mathlib.Data.ZMod.Basic
public import Definitions.Def_LeanPool_PureNock_ModularEval
set_option autoImplicit true
@[expose] public section
public section
open Nock Nock.FieldEmbedding
open Nock Nock.Noun

theorem Nock.FieldEmbedding.edit_boundedBy (q : ℕ) (ax : Nat) (new old : Noun) :
    BoundedBy q new → BoundedBy q old →
      ∀ {m : Noun}, edit ax new old = some m → BoundedBy q m := by sorry
