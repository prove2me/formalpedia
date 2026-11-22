-- Prove2me | Theorems.Thm_Nock_evalPaperMod_boundedBy
-- name    : Nock.evalPaperMod_boundedBy
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:28:11.481495+00:00
-- url     : https://prove2.me/theorems/ff82f9ef-c3a5-4279-b033-c903437ac3ae
-- title:
--   Nock: eval Paper Mod bounded By
-- statement:
--   **`evalPaperMod q` preserves `q`-boundedness (unconditionally).**  On canonical field-noun
--       inputs (`BoundedBy q`), every successful modular run returns a canonical field noun — the
--       modular oracle maps `𝒩(𝔽)` into `𝒩(𝔽)`, handling the wrap exactly (no guard needed).
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/PaperReferenceMod.lean#L149-L152
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/PaperReferenceMod.lean#L149-L152

module
public import Definitions.Def_LeanPool_PureNock_PaperReference
public import Definitions.Def_LeanPool_PureNock_ModularEval
public import Definitions.Def_LeanPool_PureNock_PaperReferenceMod
set_option autoImplicit true
@[expose] public section
public section
open Nock
open Noun

theorem Nock.evalPaperMod_boundedBy {q fuel : Nat} {s f r : Noun} (hq : 1 < q)
    (hs : FieldEmbedding.BoundedBy q s) (hf : FieldEmbedding.BoundedBy q f)
    (h : evalPaperMod q fuel s f = some r) : FieldEmbedding.BoundedBy q r := by sorry
