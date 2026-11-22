-- Prove2me | Theorems.Thm_Nock_Verb_runHintProgram_output_unique
-- name    : Nock.Verb.runHintProgram_output_unique
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:29:32.874034+00:00
-- url     : https://prove2.me/theorems/f83f8e34-1ba4-4d19-b6f1-03177a3cca19
-- title:
--   Verb: run Hint Program output unique
-- statement:
--   **`runHintProgram` output uniqueness.**  Any two successful OP₁₁-extended runs of `*[s f]`, at
--       any fuel budgets, return the same noun.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/Determinism.lean#L45-L50
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/Determinism.lean#L45-L50

module
public import Definitions.Def_LeanPool_PureNock_PureCompleteHint
public import Definitions.Def_LeanPool_PureNock_PaperReferenceMod
public import Definitions.Def_LeanPool_PureNock_Determinism
set_option autoImplicit true
@[expose] public section
public section
open Nock
open Nock.Verb

theorem Nock.Verb.runHintProgram_output_unique {s f r₁ r₂ : Noun}
    (h₁ : ∃ fuel, runHintProgram fuel s f = some r₁)
    (h₂ : ∃ fuel, runHintProgram fuel s f = some r₂) : r₁ = r₂ := by sorry
