-- Prove2me | Theorems.Thm_Nock_evalGPaper_le_evalGBy
-- name    : Nock.evalGPaper_le_evalGBy
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:18:17.339805+00:00
-- url     : https://prove2.me/theorems/b557a7a3-da54-40fa-85a8-e0469a90aff6
-- title:
--   Nock: eval GPaper le eval GBy
-- statement:
--   **`evalGPaper q` refines `evalGBy q`.**  The guarded fragment run is a guarded full run with
--       the same value; they differ only where `evalGBy` fires OP₁₁, which the fragment crashes on.
--       This is what makes `FieldEmbedding.agreeBy` reusable inside the fragment.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/PaperFieldBridge.lean#L166-L171
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/PaperFieldBridge.lean#L166-L171

module
public import Definitions.Def_LeanPool_PureNock_PaperReferenceMod
public import Definitions.Def_LeanPool_PureNock_PureComplete
public import Definitions.Def_LeanPool_PureNock_PaperFieldBridge
set_option autoImplicit true
@[expose] public section
public section
open Nock
open Noun

theorem Nock.evalGPaper_le_evalGBy {q n : Nat} {s form r : Noun}
    (h : evalGPaper q n s form = some r) : FieldEmbedding.evalGBy q n s form = some r := by sorry
