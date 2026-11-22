-- Prove2me | Theorems.Thm_Nock_Verb_runProgram_output_unique
-- name    : Nock.Verb.runProgram_output_unique
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:29:29.76137+00:00
-- url     : https://prove2.me/theorems/a2d747c5-4d4f-48fa-9e15-b088109e2efe
-- title:
--   Verb: run Program output unique
-- statement:
--   **`runProgram` output uniqueness.**  Any two successful small-step runs of `*[s f]`, at any
--       fuel budgets, return the same noun.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/Determinism.lean#L36-L41
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/Determinism.lean#L36-L41

module
public import Definitions.Def_LeanPool_PureNock_PureCompleteHint
public import Definitions.Def_LeanPool_PureNock_PaperReferenceMod
public import Definitions.Def_LeanPool_PureNock_Determinism
set_option autoImplicit true
@[expose] public section
public section
open Nock
open Nock.Verb

theorem Nock.Verb.runProgram_output_unique {s f r₁ r₂ : Noun}
    (h₁ : ∃ fuel, runProgram fuel s f = some r₁)
    (h₂ : ∃ fuel, runProgram fuel s f = some r₂) : r₁ = r₂ := by sorry
