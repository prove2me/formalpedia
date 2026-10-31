-- Prove2me | Theorems.Thm_OAI_Generator_Tracial_represented_four_selfAdjoint_generators_q129
-- name    : OAI.Generator.Tracial.represented_four_selfAdjoint_generators_q129
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-30T20:40:59.707432+00:00
-- url     : https://prove2.me/theorems/afe8efd9-3cb3-4c8b-af1c-e5f692546014
-- title:
--   OAI.Generator.Tracial.represented_four_selfAdjoint_generators_q129: intermediate lemma from OpenAI, Relative generation and the generator problem for finite factors
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.RelativeGeneration.main_theorem` and `OAI.Generator.single_generation_of_II1_separable_predual`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Relative generation and the generator problem for finite factors*, OpenAI Math Release, September 23, 2026, result family 296, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Generator.Tracial.represented_four_selfAdjoint_generators` of [lean/OAI/Analysis/FactorGeneration/Generation.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/FactorGeneration/Generation.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Generator.Tracial`, with `open Filter`, `open scoped Topology`, `open scoped ComplexStarModule`, `open UltrapowerBridge`):
--
--   ```lean
--   theorem represented_four_selfAdjoint_generators_q129 (τ : TracialRepresentation M)
--       (hfactor : ∀ c : M.toStarSubalgebra,
--         (∀ a : M.toStarSubalgebra,a*c=c*a) → ∃ z : ℂ,c=z • (1 : M.toStarSubalgebra))
--       (hdiff : ∀ p : M.toStarSubalgebra,IsStarProjection p → p ≠ 0 →
--         ∃ q : M.toStarSubalgebra,IsStarProjection q ∧ q ≠ 0 ∧ q ≠ p ∧ p*q=q ∧ q*p=q)
--       (hsep : TopologicalSpace.IsSeparable (Set.range (baseVector τ))) :
--       ∃ a ∈ M,∃ b ∈ M,∃ c ∈ M,∃ d ∈ M,
--         IsSelfAdjoint a ∧ IsSelfAdjoint b ∧ IsSelfAdjoint c ∧ IsSelfAdjoint d ∧
--         wstar {a,b,c,d}=M.toStarSubalgebra
--   ```
--
--   **Definitions.** The statement is written with `OAI.UltrapowerBridge.TracialRepresentation` (definitions bundle `OAIQ129G001` of this split); `OAI.Generator.Tracial.baseVector` (definitions bundle `OAIQ129G008` of this split); `OAI.Generator.wstar` (the published bundle `Def_FactorGeneration`).
--
--   **Used by.** The proof of `OAI.Generator.single_generation_of_II1_separable_predual` of this split imports it.
-- source:
--   OpenAI, Relative generation and the generator problem for finite factors, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 296; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Relative-generation-and-the-generator-problem-for-finite-factors-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/FactorGeneration/Generation.lean (declaration OAI.Generator.Tracial.represented_four_selfAdjoint_generators)

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_FactorGeneration
import Definitions.Def_OAIQ129G008

section

attribute [-instance] _root_.OAI.Generator.Tracial.algebraDualNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.Generator.Tracial.functionalSubspaceWeakLocallyConvex _root_.OAI.Generator.predualAlgebraDualNormed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] OAI.closedSubmoduleNormedAddCommGroup OAI.closedSubmoduleNormedSpace OAI.closedSubmoduleInner

namespace OAI

noncomputable section

namespace Generator.Tracial

open Filter
open scoped Topology

open scoped ComplexStarModule
section
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}

theorem represented_four_selfAdjoint_generators_q129 (τ : TracialRepresentation M)
    (hfactor : ∀ c : M.toStarSubalgebra,
      (∀ a : M.toStarSubalgebra,a*c=c*a) → ∃ z : ℂ,c=z • (1 : M.toStarSubalgebra))
    (hdiff : ∀ p : M.toStarSubalgebra,IsStarProjection p → p ≠ 0 →
      ∃ q : M.toStarSubalgebra,IsStarProjection q ∧ q ≠ 0 ∧ q ≠ p ∧ p*q=q ∧ q*p=q)
    (hsep : TopologicalSpace.IsSeparable (Set.range (baseVector τ))) :
    ∃ a ∈ M,∃ b ∈ M,∃ c ∈ M,∃ d ∈ M,
      IsSelfAdjoint a ∧ IsSelfAdjoint b ∧ IsSelfAdjoint c ∧ IsSelfAdjoint d ∧
      wstar {a,b,c,d}=M.toStarSubalgebra := by
  sorry

end

open UltrapowerBridge

end Generator.Tracial

end

end OAI
end
