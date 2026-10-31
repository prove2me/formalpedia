-- Prove2me | Theorems.Thm_OAI_Generator_FiniteMatrixStage_exists_matrix_generated_centered_partition
-- name    : OAI.Generator.FiniteMatrixStage.exists_matrix_generated_centered_partition
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-30T09:45:56.183983+00:00
-- url     : https://prove2.me/theorems/1d138fff-1671-465d-9b10-425dbb610d84
-- title:
--   OAI.Generator.FiniteMatrixStage.exists_matrix_generated_centered_partition: intermediate lemma from OpenAI, Relative generation and the generator problem for finite factors
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Generator.single_generation_of_II1_separable_predual`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Relative generation and the generator problem for finite factors*, OpenAI Math Release, September 23, 2026, result family 296, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Generator.FiniteMatrixStage.exists_matrix_generated_centered_partition` of [lean/OAI/Analysis/FactorGeneration/MatrixExpectation.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/FactorGeneration/MatrixExpectation.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Generator.FiniteMatrixStage`, with `open Filter`, `open scoped Topology`, `open Filter`, `open scoped BigOperators Topology`, `open UltrapowerBridge Tracial`):
--
--   ```lean
--   theorem exists_matrix_generated_centered_partition (A : ℕ → FiniteMatrixStage N)
--       (hA : Monotone (fun n => (A n).units.concreteAlgebra))
--       (τ : TracialRepresentation (generatedVonNeumann A))
--       (hfactor : IsII1Factor (generated A))
--       {ι : Type*} (F : Finset ι) (x : ι → (generatedVonNeumann A).toStarSubalgebra)
--       (ht : ∀ i ∈ F,τ.trace (x i)=0) (ε : ℝ) (hε : 0 < ε) :
--       ∃ Q : CornerPartition (identityProjection (generatedVonNeumann A)),
--         (∑ i ∈ F,τ.norm₂ (Q.pinch (x i))^2) < ε
--   ```
--
--   **Definitions.** The statement is written with `OAI.Generator.FiniteMatrixStage`, `OAI.UltrapowerBridge.TracialRepresentation`, `OAI.UltrapowerBridge.TracialRepresentation.norm₂` and `OAI.UltrapowerBridge.TracialRepresentation.trace` (definitions bundle `OAIQ11Fg000` of this split); `OAI.Generator.Tracial.CornerPartition`, `OAI.Generator.Tracial.identityProjection` and `OAI.Generator.Tracial.CornerPartition.pinch` (definitions bundle `OAIQ11Fg001` of this split); `OAI.Generator.FiniteMatrixStage.generated` and `OAI.Generator.MatrixUnitSystem.concreteAlgebra` (definitions bundle `OAIQ11Fg003` of this split); `OAI.Generator.FiniteMatrixStage.generatedVonNeumann` (definitions bundle `OAIQ11Fg007` of this split); `OAI.Generator.IsII1Factor` (the published bundle `Def_FactorGeneration`).
--
--   **Used by.** The proof of `OAI.Generator.Tracial.exists_unitResidual_local_compression` of this split imports it.
-- source:
--   OpenAI, Relative generation and the generator problem for finite factors, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 296; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Relative-generation-and-the-generator-problem-for-finite-factors-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/FactorGeneration/MatrixExpectation.lean (declaration OAI.Generator.FiniteMatrixStage.exists_matrix_generated_centered_partition)

import Mathlib
import Definitions.Def_FactorGeneration
import Definitions.Def_OAIQ11Fg007

section

attribute [-instance] _root_.OAI.Generator.CoefficientOrder.coefficientPartialOrder _root_.OAI.Generator.Tracial.algebraDualNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.Generator.Tracial.functionalSubspaceWeakLocallyConvex _root_.OAI.Generator.predualAlgebraDualNormed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] OAI.closedSubmoduleNormedAddCommGroup OAI.closedSubmoduleNormedSpace OAI.closedSubmoduleInner OAI.vonNeumannToStarSubalgebraIsClosed

namespace OAI

noncomputable section

namespace Generator

open Filter
open scoped Topology

open Filter
open scoped BigOperators Topology
namespace FiniteMatrixStage

section
open UltrapowerBridge Tracial
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {N : VonNeumannAlgebra H}

theorem exists_matrix_generated_centered_partition (A : ℕ → FiniteMatrixStage N)
    (hA : Monotone (fun n => (A n).units.concreteAlgebra))
    (τ : TracialRepresentation (generatedVonNeumann A))
    (hfactor : IsII1Factor (generated A))
    {ι : Type*} (F : Finset ι) (x : ι → (generatedVonNeumann A).toStarSubalgebra)
    (ht : ∀ i ∈ F,τ.trace (x i)=0) (ε : ℝ) (hε : 0 < ε) :
    ∃ Q : CornerPartition (identityProjection (generatedVonNeumann A)),
      (∑ i ∈ F,τ.norm₂ (Q.pinch (x i))^2) < ε := by
  sorry

end

open UltrapowerBridge Tracial

end FiniteMatrixStage

open Filter
open scoped Topology

end Generator

end

end OAI
end
