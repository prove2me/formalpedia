-- Prove2me | Theorems.Thm_OAI_Generator_Tracial_exists_scalar_pinching_for_matrixUnits_q129
-- name    : OAI.Generator.Tracial.exists_scalar_pinching_for_matrixUnits_q129
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-30T20:24:00.604848+00:00
-- url     : https://prove2.me/theorems/d8a5268d-186d-48ab-8ca4-f39fc03e518e
-- title:
--   OAI.Generator.Tracial.exists_scalar_pinching_for_matrixUnits_q129: intermediate lemma from OpenAI, Relative generation and the generator problem for finite factors
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.RelativeGeneration.main_theorem` and `OAI.Generator.single_generation_of_II1_separable_predual`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Relative generation and the generator problem for finite factors*, OpenAI Math Release, September 23, 2026, result family 296, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Generator.Tracial.exists_scalar_pinching_for_matrixUnits` of [lean/OAI/Analysis/FactorGeneration/MatrixExpectation.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/FactorGeneration/MatrixExpectation.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Generator.Tracial`, with `open Filter`, `open scoped Topology`, `open UltrapowerBridge`):
--
--   ```lean
--   theorem exists_scalar_pinching_for_matrixUnits_q129
--       (hfactor : ∀ c : M.toStarSubalgebra,
--         (∀ a : M.toStarSubalgebra,a*c=c*a) → ∃ z : ℂ,c=z • (1 : M.toStarSubalgebra))
--       (hdiff : ∀ p : M.toStarSubalgebra,IsStarProjection p → p ≠ 0 →
--         ∃ q : M.toStarSubalgebra,IsStarProjection q ∧ q ≠ 0 ∧ q ≠ p ∧ p*q=q ∧ q*p=q)
--       {n : ℕ} (hn : 0 < n) (E : MatrixUnitSystem (Fin n) M.toStarSubalgebra) :
--       ∃ Q : CornerPartition (identityProjection M),
--         ∀ x : M.toStarSubalgebra,x ∈ E.algebra → Q.pinch x=τ.trace x • (1 : M.toStarSubalgebra)
--   ```
--
--   **Definitions.** The statement is written with `OAI.Generator.Tracial.CornerPartition` and `OAI.Generator.Tracial.CornerPartition.pinch` (definitions bundle `OAIQ129G000` of this split); `OAI.Generator.MatrixUnitSystem`, `OAI.UltrapowerBridge.TracialRepresentation`, `OAI.Generator.MatrixUnitSystem.algebra` and `OAI.UltrapowerBridge.TracialRepresentation.trace` (definitions bundle `OAIQ129G001` of this split); `OAI.Generator.Tracial.identityProjection` (definitions bundle `OAIQ129G005` of this split).
--
--   **Used by.** The proof of `OAI.Generator.Tracial.exists_unitResidual_local_compression_q129` of this split imports it.
-- source:
--   OpenAI, Relative generation and the generator problem for finite factors, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 296; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Relative-generation-and-the-generator-problem-for-finite-factors-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/FactorGeneration/MatrixExpectation.lean (declaration OAI.Generator.Tracial.exists_scalar_pinching_for_matrixUnits)

import Mathlib
import Definitions.Def_OAIQ129G005

section

attribute [-instance] _root_.OAI.Generator.CoefficientOrder.coefficientPartialOrder _root_.OAI.Generator.Tracial.algebraDualNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.Generator.Tracial.functionalSubspaceWeakLocallyConvex _root_.OAI.Generator.predualAlgebraDualNormed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] OAI.closedSubmoduleNormedAddCommGroup OAI.closedSubmoduleNormedSpace OAI.closedSubmoduleInner

namespace OAI

noncomputable section

namespace Generator

open Filter
open scoped Topology

namespace Tracial
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H} (τ : TracialRepresentation M)

theorem exists_scalar_pinching_for_matrixUnits_q129
    (hfactor : ∀ c : M.toStarSubalgebra,
      (∀ a : M.toStarSubalgebra,a*c=c*a) → ∃ z : ℂ,c=z • (1 : M.toStarSubalgebra))
    (hdiff : ∀ p : M.toStarSubalgebra,IsStarProjection p → p ≠ 0 →
      ∃ q : M.toStarSubalgebra,IsStarProjection q ∧ q ≠ 0 ∧ q ≠ p ∧ p*q=q ∧ q*p=q)
    {n : ℕ} (hn : 0 < n) (E : MatrixUnitSystem (Fin n) M.toStarSubalgebra) :
    ∃ Q : CornerPartition (identityProjection M),
      ∀ x : M.toStarSubalgebra,x ∈ E.algebra → Q.pinch x=τ.trace x • (1 : M.toStarSubalgebra) := by
  sorry

end Tracial

open Filter
open scoped BigOperators Topology

open Filter
open scoped Topology

end Generator

end

end OAI
end
