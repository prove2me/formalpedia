-- Prove2me | Theorems.Thm_Nock_FieldEmbedding_embBy_atom
-- name    : Nock.FieldEmbedding.embBy_atom
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:18:23.293804+00:00
-- url     : https://prove2.me/theorems/e3eb18f2-38eb-4e02-8244-7e85edb0bb72
-- title:
--   Field Embedding: emb By atom
-- statement:
--   The Field Embedding construction uses the emb By atom property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/PaperFieldBridge.lean#L213-L213
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/PaperFieldBridge.lean#L213-L213

module
public import Definitions.Def_LeanPool_PureNock_PaperReferenceMod
public import Definitions.Def_LeanPool_PureNock_PureComplete
public import Definitions.Def_LeanPool_PureNock_PaperFieldBridge
set_option autoImplicit true
@[expose] public section
public section
open Nock
open Noun
open Nock.FieldEmbedding

theorem Nock.FieldEmbedding.embBy_atom {q n : Nat} : embBy q (.atom n) = .atom (n : ZMod q) := by sorry

attribute [defeq] Nock.FieldEmbedding.embBy_atom
