-- Prove2me | Theorems.Thm_OAI_Generator_Tracial_represented_relative_generation_q129
-- name    : OAI.Generator.Tracial.represented_relative_generation_q129
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-30T20:45:54.549001+00:00
-- url     : https://prove2.me/theorems/bff55ca0-e61f-4823-94e4-890c73f9b2ab
-- title:
--   OAI.Generator.Tracial.represented_relative_generation_q129: intermediate lemma from OpenAI, Relative generation and the generator problem for finite factors
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.RelativeGeneration.main_theorem` and `OAI.Generator.single_generation_of_II1_separable_predual`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Relative generation and the generator problem for finite factors*, OpenAI Math Release, September 23, 2026, result family 296, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Generator.Tracial.represented_relative_generation` of [lean/OAI/Analysis/FactorGeneration/Generation.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/FactorGeneration/Generation.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Generator.Tracial`, with `open Filter`, `open scoped Topology`, `open UltrapowerBridge`):
--
--   ```lean
--   theorem represented_relative_generation_q129 :
--       ∃ C : Set (TraceUnitary τ), IsGδ C ∧ Dense C ∧
--         ∀ u ∈ C, wstar ((N : Set (H →L[ℂ] H)) ∪ {(u.algebra τ).val})=M.toStarSubalgebra
--   ```
--
--   **Definitions.** The statement is written with `OAI.UltrapowerBridge.TracialRepresentation` and `OAI.Generator.Tracial.coordinateInclusion` (definitions bundle `OAIQ129G001` of this split); `OAI.Generator.Tracial.TraceUnitary`, `OAI.Generator.Tracial.baseVector`, `OAI.Generator.Tracial.TraceUnitary.algebra` and `OAI.Generator.Tracial.TraceUnitary.instMetricSpace` (definitions bundle `OAIQ129G008` of this split); `OAI.Generator.wstar` (the published bundle `Def_FactorGeneration`).
--
--   **Used by.** The proofs of `OAI.Generator.Tracial.represented_four_selfAdjoint_generators_q129` and `OAI.RelativeGeneration.main_theorem` of this split import it.
-- source:
--   OpenAI, Relative generation and the generator problem for finite factors, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 296; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Relative-generation-and-the-generator-problem-for-finite-factors-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/FactorGeneration/Generation.lean (declaration OAI.Generator.Tracial.represented_relative_generation)

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
section
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {N M : VonNeumannAlgebra H} (τ : TracialRepresentation M)
variable (hNM : N ≤ M)
variable (hfactor : ∀ c : N.toStarSubalgebra,
  (∀ a : N.toStarSubalgebra,a*c=c*a) → ∃ z : ℂ,c=z • (1 : N.toStarSubalgebra))
variable (hdiff : ∀ r : N.toStarSubalgebra,IsStarProjection r → r ≠ 0 →
  ∃ q : N.toStarSubalgebra,IsStarProjection q ∧ q ≠ 0 ∧ q ≠ r ∧ r*q=q ∧ q*r=q)
variable (hirr : ∀ c : M.toStarSubalgebra,
  (∀ a : N.toStarSubalgebra,coordinateInclusion hNM a*c=c*coordinateInclusion hNM a) →
  ∃ z : ℂ,c=z • (1 : M.toStarSubalgebra))
variable (hsep : TopologicalSpace.IsSeparable (Set.range (baseVector τ)))
include hfactor hdiff hirr hsep

theorem represented_relative_generation_q129 :
    ∃ C : Set (TraceUnitary τ), IsGδ C ∧ Dense C ∧
      ∀ u ∈ C, wstar ((N : Set (H →L[ℂ] H)) ∪ {(u.algebra τ).val})=M.toStarSubalgebra := by
  sorry

end

open scoped ComplexStarModule

open UltrapowerBridge

end Generator.Tracial

end

end OAI
end
