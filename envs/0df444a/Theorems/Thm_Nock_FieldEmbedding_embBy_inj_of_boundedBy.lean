-- Prove2me | Theorems.Thm_Nock_FieldEmbedding_embBy_inj_of_boundedBy
-- name    : Nock.FieldEmbedding.embBy_inj_of_boundedBy
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:18:18.884832+00:00
-- url     : https://prove2.me/theorems/b5e2f62f-36ea-44bd-b464-7ab57eefe5a1
-- title:
--   Field Embedding: emb By inj of bounded By
-- statement:
--   **`embBy q` is injective on `q`-bounded nouns.**  Distinct canonical residues `< q` stay
--       distinct in `ZMod q`, so structural Nock equality is field equality there (`main.tex:1525`).
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/PaperFieldBridge.lean#L217-L234
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/PaperFieldBridge.lean#L217-L234

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

theorem Nock.FieldEmbedding.embBy_inj_of_boundedBy {q : Nat} :
    ∀ {a b : Noun}, BoundedBy q a → BoundedBy q b → embBy q a = embBy q b → a = b := by sorry
