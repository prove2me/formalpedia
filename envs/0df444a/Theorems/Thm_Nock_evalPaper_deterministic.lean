-- Prove2me | Theorems.Thm_Nock_evalPaper_deterministic
-- name    : Nock.evalPaper_deterministic
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:11:04.442031+00:00
-- url     : https://prove2.me/theorems/31869e86-9c55-4013-b3fd-cf8e627635f6
-- title:
--   Nock: eval Paper deterministic
-- statement:
--   **`evalPaper` is a partial function (output uniqueness).**  Two successful paper-fragment
--       evaluations of the same `subject`/`formula`, at any fuel budgets, return the same noun.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/PaperReference.lean#L115-L118
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/PaperReference.lean#L115-L118

module
public import Definitions.Def_LeanPool_PureNock_Reference
public import Definitions.Def_LeanPool_PureNock_PaperReference
set_option autoImplicit true
@[expose] public section
public section
open Nock
open Noun

theorem Nock.evalPaper_deterministic {n m : Nat} {s form r₁ r₂ : Noun}
    (h₁ : evalPaper n s form = some r₁) (h₂ : evalPaper m s form = some r₂) : r₁ = r₂ := by sorry
