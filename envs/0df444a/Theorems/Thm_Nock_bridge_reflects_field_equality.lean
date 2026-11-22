-- Prove2me | Theorems.Thm_Nock_bridge_reflects_field_equality
-- name    : Nock.bridge_reflects_field_equality
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:29:13.956038+00:00
-- url     : https://prove2.me/theorems/c83d8bde-7be7-4767-8a8c-d248767c211d
-- title:
--   Nock: bridge reflects field equality
-- statement:
--   **The bridge carries the equivalence through the field embedding.**  Two guarded fragment runs
--       on `q`-bounded inputs whose results have the same field image have the *same result noun*: the
--       no-overflow conditional yields boundedness, and boundedness yields injectivity.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/PaperFieldBridge.lean#L283-L292
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/PaperFieldBridge.lean#L283-L292

module
public import Definitions.Def_LeanPool_PureNock_PaperReferenceMod
public import Definitions.Def_LeanPool_PureNock_PureComplete
public import Definitions.Def_LeanPool_PureNock_PaperFieldBridge
set_option autoImplicit true
@[expose] public section
public section
open Nock
open Noun

theorem Nock.bridge_reflects_field_equality (q : Nat) (hq : 1 < q)
    {fuel₁ fuel₂ : Nat} {s₁ f₁ s₂ f₂ r₁ r₂ : Noun}
    (hs₁ : FieldEmbedding.BoundedBy q s₁) (hf₁ : FieldEmbedding.BoundedBy q f₁)
    (hs₂ : FieldEmbedding.BoundedBy q s₂) (hf₂ : FieldEmbedding.BoundedBy q f₂)
    (hG₁ : evalGPaper q fuel₁ s₁ f₁ = some r₁)
    (hG₂ : evalGPaper q fuel₂ s₂ f₂ = some r₂)
    (himg : FieldEmbedding.embBy q r₁ = FieldEmbedding.embBy q r₂) : r₁ = r₂ := by sorry
