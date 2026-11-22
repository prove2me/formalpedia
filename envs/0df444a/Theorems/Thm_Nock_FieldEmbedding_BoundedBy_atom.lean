-- Prove2me | Theorems.Thm_Nock_FieldEmbedding_BoundedBy_atom
-- name    : Nock.FieldEmbedding.BoundedBy_atom
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T11:59:49.068926+00:00
-- url     : https://prove2.me/theorems/acf859ee-317a-41fc-a8fb-e7af3443c8a4
-- title:
--   Field Embedding: Bounded By atom
-- statement:
--   The Field Embedding construction uses the Bounded By atom property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/ModularEval.lean#L51-L51
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/ModularEval.lean#L51-L51

module
public import Definitions.Def_LeanPool_PureNock_Reference
public import Mathlib.Data.ZMod.Basic
public import Definitions.Def_LeanPool_PureNock_ModularEval
set_option autoImplicit true
@[expose] public section
public section
open Nock Nock.FieldEmbedding
open Nock Nock.Noun

theorem Nock.FieldEmbedding.BoundedBy_atom {q n : ℕ} : BoundedBy q (.atom n) ↔ n < q := by sorry
