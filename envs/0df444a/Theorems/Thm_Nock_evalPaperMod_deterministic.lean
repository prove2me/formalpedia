-- Prove2me | Theorems.Thm_Nock_evalPaperMod_deterministic
-- name    : Nock.evalPaperMod_deterministic
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:29:35.198203+00:00
-- url     : https://prove2.me/theorems/27cebb79-8c58-4558-bd81-6341be68a227
-- title:
--   Nock: eval Paper Mod deterministic
-- statement:
--   **`evalPaperMod q` is a partial function (output uniqueness).**  Two successful modular
--       fragment evaluations of the same `subject`/`formula`, at any fuel budgets, agree.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/Determinism.lean#L56-L59
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/Determinism.lean#L56-L59

module
public import Definitions.Def_LeanPool_PureNock_PureCompleteHint
public import Definitions.Def_LeanPool_PureNock_PaperReferenceMod
public import Definitions.Def_LeanPool_PureNock_Determinism
set_option autoImplicit true
@[expose] public section
public section
open Nock

theorem Nock.evalPaperMod_deterministic {q n m : Nat} {s form r₁ r₂ : Noun}
    (h₁ : evalPaperMod q n s form = some r₁) (h₂ : evalPaperMod q m s form = some r₂) : r₁ = r₂ := by sorry
