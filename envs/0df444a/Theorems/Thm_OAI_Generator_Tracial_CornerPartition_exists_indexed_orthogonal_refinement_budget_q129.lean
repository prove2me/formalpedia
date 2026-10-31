-- Prove2me | Theorems.Thm_OAI_Generator_Tracial_CornerPartition_exists_indexed_orthogonal_refinement_budget_q129
-- name    : OAI.Generator.Tracial.CornerPartition.exists_indexed_orthogonal_refinement_budget_q129
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-30T20:40:03.124628+00:00
-- url     : https://prove2.me/theorems/03c78173-c877-44e2-a6af-1749ebd63ba9
-- title:
--   OAI.Generator.Tracial.CornerPartition.exists_indexed_orthogonal_refinement_budget_q129: intermediate lemma from OpenAI, Relative generation and the generator problem for finite factors
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.RelativeGeneration.main_theorem` and `OAI.Generator.single_generation_of_II1_separable_predual`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Relative generation and the generator problem for finite factors*, OpenAI Math Release, September 23, 2026, result family 296, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Generator.Tracial.CornerPartition.exists_indexed_orthogonal_refinement_budget` of [lean/OAI/Analysis/FactorGeneration/EnergyDescent.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/FactorGeneration/EnergyDescent.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Generator.Tracial.CornerPartition`, with `open scoped BigOperators Topology`, `open Filter`, `open UltrapowerBridge`):
--
--   ```lean
--   theorem exists_indexed_orthogonal_refinement_budget_q129
--       (Q : CornerPartition (identityProjection M))
--       (hN : ∀ i,(Q.piece i).val.val ∈ N)
--       {ι : Type*} (F : Finset ι) (v : ι → M.toStarSubalgebra)
--       (hF : ∀ x ∈ F,TraceOrthogonal τ (insideAlgebra (M := M) (P := N)) (v x))
--       (b : ℝ) (hb : 0 < b) :
--       ∃ R : CornerPartition (identityProjection M), Q.Refines R ∧
--         (∀ i,(R.piece i).val.val ∈ N) ∧ (∑ x ∈ F,τ.norm₂ (R.pinch (v x))^2) < b
--   ```
--
--   **Definitions.** The statement is written with `OAI.Generator.Tracial.CornerPartition` and `OAI.Generator.Tracial.CornerPartition.pinch` (definitions bundle `OAIQ129G000` of this split); `OAI.UltrapowerBridge.TracialRepresentation`, `OAI.Generator.Tracial.insideAlgebra` and `OAI.UltrapowerBridge.TracialRepresentation.norm₂` (definitions bundle `OAIQ129G001` of this split); `OAI.Generator.Tracial.identityProjection` and `OAI.Generator.Tracial.CornerPartition.Refines` (definitions bundle `OAIQ129G005` of this split); `OAI.Generator.Tracial.TraceOrthogonal` (definitions bundle `OAIQ129G008` of this split).
--
--   **Used by.** The proof of `OAI.Generator.Tracial.exists_unitResidual_local_compression_q129` of this split imports it.
-- source:
--   OpenAI, Relative generation and the generator problem for finite factors, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 296; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Relative-generation-and-the-generator-problem-for-finite-factors-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/FactorGeneration/EnergyDescent.lean (declaration OAI.Generator.Tracial.CornerPartition.exists_indexed_orthogonal_refinement_budget)

import Mathlib
import Definitions.Def_OAIQ129G008

section

attribute [-instance] _root_.OAI.Generator.CoefficientOrder.coefficientPartialOrder _root_.OAI.Generator.Tracial.TraceUnitary.instMetricSpace _root_.OAI.Generator.Tracial.algebraDualNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.Generator.Tracial.functionalSubspaceWeakLocallyConvex _root_.OAI.Generator.predualAlgebraDualNormed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] OAI.closedSubmoduleNormedAddCommGroup OAI.closedSubmoduleNormedSpace OAI.closedSubmoduleInner

namespace OAI

noncomputable section

namespace Generator.Tracial

section
open scoped BigOperators Topology
open Filter
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {N M : VonNeumannAlgebra H} (τ : TracialRepresentation M)
namespace CornerPartition
variable (hNM : N ≤ M)
variable (hirr : ∀ c : M.toStarSubalgebra,
  (∀ a : insideAlgebra (M := M) (P := N),
    (a : M.toStarSubalgebra)*c=c*(a : M.toStarSubalgebra)) →
  ∃ z : ℂ,c=z • (1 : M.toStarSubalgebra))
include hNM hirr

theorem exists_indexed_orthogonal_refinement_budget_q129
    (Q : CornerPartition (identityProjection M))
    (hN : ∀ i,(Q.piece i).val.val ∈ N)
    {ι : Type*} (F : Finset ι) (v : ι → M.toStarSubalgebra)
    (hF : ∀ x ∈ F,TraceOrthogonal τ (insideAlgebra (M := M) (P := N)) (v x))
    (b : ℝ) (hb : 0 < b) :
    ∃ R : CornerPartition (identityProjection M), Q.Refines R ∧
      (∀ i,(R.piece i).val.val ∈ N) ∧ (∑ x ∈ F,τ.norm₂ (R.pinch (v x))^2) < b := by
  sorry

end CornerPartition

end

open scoped BigOperators
open UltrapowerBridge

end Generator.Tracial

end

end OAI
end
