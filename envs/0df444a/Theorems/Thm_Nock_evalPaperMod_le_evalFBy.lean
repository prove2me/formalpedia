-- Prove2me | Theorems.Thm_Nock_evalPaperMod_le_evalFBy
-- name    : Nock.evalPaperMod_le_evalFBy
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:06:13.945199+00:00
-- url     : https://prove2.me/theorems/8cd5d98c-c92e-4916-a1aa-93e6de465187
-- title:
--   Nock: eval Paper Mod le eval FBy
-- statement:
--   **`evalPaperMod q` refines `evalFBy q`.** Every strict-paper modular evaluation is a full
--       modular evaluation with the same result: they differ only where `evalFBy` fires OP₁₁, which
--       `evalPaperMod` crashes on.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/PaperReferenceMod.lean#L138-L143
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/PaperReferenceMod.lean#L138-L143

module
public import Definitions.Def_LeanPool_PureNock_PaperReference
public import Definitions.Def_LeanPool_PureNock_ModularEval
public import Definitions.Def_LeanPool_PureNock_PaperReferenceMod
set_option autoImplicit true
@[expose] public section
public section
open Nock
open Noun

theorem Nock.evalPaperMod_le_evalFBy {q n : Nat} {s form r : Noun}
    (h : evalPaperMod q n s form = some r) : FieldEmbedding.evalFBy q n s form = some r := by sorry
