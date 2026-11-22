-- Prove2me | Theorems.Thm_Nock_FieldEmbedding_evalGBy_le_evalN
-- name    : Nock.FieldEmbedding.evalGBy_le_evalN
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:27:56.926806+00:00
-- url     : https://prove2.me/theorems/fc3a6808-1d7b-492a-92ae-614551eba10e
-- title:
--   Field Embedding: eval GBy le eval N
-- statement:
--   The Field Embedding construction uses the eval GBy le eval N property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/ModularEval.lean#L557-L560
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/ModularEval.lean#L557-L560

module
public import Definitions.Def_LeanPool_PureNock_Reference
public import Mathlib.Data.ZMod.Basic
public import Definitions.Def_LeanPool_PureNock_ModularEval
set_option autoImplicit true
@[expose] public section
public section
open Nock Nock.FieldEmbedding
open Nock Nock.Noun

theorem Nock.FieldEmbedding.evalGBy_le_evalN {q : ℕ} (hq : 1 < q) {fuel : Nat} {s f r : Noun}
    (hs : BoundedBy q s) (hf : BoundedBy q f) (h : evalGBy q fuel s f = some r) :
    evalN fuel s f = some r := by sorry
