-- Prove2me | Theorems.Thm_OAI_TuringRigidity_RelativeConstructible_seed_bound_stage_at_levels
-- name    : OAI.TuringRigidity.RelativeConstructible.seed_bound_stage_at_levels
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T00:46:37.607702+00:00
-- url     : https://prove2.me/theorems/60447fee-25eb-4364-aa70-30cc24a66cac
-- title:
--   OAI.TuringRigidity.RelativeConstructible.seed_bound_stage_at_levels: intermediate lemma from OpenAI, Rigidity of the Turing degrees (result family 241)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.TuringRigidity.ManuscriptMain.rigidity`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Rigidity of the Turing degrees (result family 241)*, OpenAI Math Release, September 24, 2026, result family 241, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.TuringRigidity.RelativeConstructible.seed_bound_stage_at_levels` of [lean/OAI/Computability/DegreeRigidity/Constructibility/SeedBoundStageSyntax.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/DegreeRigidity/Constructibility/SeedBoundStageSyntax.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.TuringRigidity.RelativeConstructible`, with `open ElementaryModel BoundedSetTheory TransitiveNameModel SentenceCoding`, `open BoundedDefinability SetModelFunctions`):
--
--   ```lean
--   theorem seed_bound_stage_at_levels (M x : ZFSet.{u}) (hM : Transitive M) (hT : SourceT M)
--       (hx : x ∈ relativeModel M (groundReals M)) :
--       ∃ γ : Ordinal.{u}, γ.toZFSet ∈ M ∧
--         ∀ δ : Ordinal.{u}, δ.toZFSet ∈ M → γ ≤ δ →
--           x ∈ level (groundReals M) δ ∧ stage (groundReals M) x ∈ level (groundReals M) δ ∧
--           ∀ A : ZFSet.{u}, SeedBoundStage (level (groundReals M) δ) ZFSet.omega
--             (ZFSet.prod ZFSet.omega ZFSet.omega) (groundReals M) x A ↔ A = stage (groundReals M) x
--   ```
--
--   **Definitions.** The statement is written with `OAI.TuringRigidity.TransitiveNameModel.Transitive` (definitions bundle `OAIQ064A000` of this split); `OAI.TuringRigidity.RelativeConstructible.groundReals` (definitions bundle `OAIQ064A001` of this split); `OAI.TuringRigidity.BoundedSetTheory.SourceT` (definitions bundle `OAIQ064A002` of this split); `OAI.TuringRigidity.RelativeConstructible.SeedBoundStage`, `OAI.TuringRigidity.RelativeConstructible.level`, `OAI.TuringRigidity.RelativeConstructible.relativeModel` and `OAI.TuringRigidity.RelativeConstructible.stage` (definitions bundle `OAIQ064A007` of this split).
--
--   **Used by.** The proof of `OAI.TuringRigidity.RelativeConstructible.Construction.largest_domain_definition` of this split imports it.
-- source:
--   OpenAI, Rigidity of the Turing degrees (result family 241), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 241; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Rigidity-of-the-Turing-degrees-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/DegreeRigidity/Constructibility/SeedBoundStageSyntax.lean (declaration OAI.TuringRigidity.RelativeConstructible.seed_bound_stage_at_levels)

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_OAIQ064A007

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.RelativeConstructible
open ElementaryModel BoundedSetTheory TransitiveNameModel SentenceCoding
open BoundedDefinability SetModelFunctions
universe u

theorem seed_bound_stage_at_levels (M x : ZFSet.{u}) (hM : Transitive M) (hT : SourceT M)
    (hx : x ∈ relativeModel M (groundReals M)) :
    ∃ γ : Ordinal.{u}, γ.toZFSet ∈ M ∧
      ∀ δ : Ordinal.{u}, δ.toZFSet ∈ M → γ ≤ δ →
        x ∈ level (groundReals M) δ ∧ stage (groundReals M) x ∈ level (groundReals M) δ ∧
        ∀ A : ZFSet.{u}, SeedBoundStage (level (groundReals M) δ) ZFSet.omega
          (ZFSet.prod ZFSet.omega ZFSet.omega) (groundReals M) x A ↔ A = stage (groundReals M) x := by
  sorry

end TuringRigidity.RelativeConstructible

end OAI
end
