-- Prove2me | Theorems.Thm_OAI_Generator_Tracial_exists_unitResidual_local_compression_q129
-- name    : OAI.Generator.Tracial.exists_unitResidual_local_compression_q129
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-30T20:54:12.605996+00:00
-- url     : https://prove2.me/theorems/71eafb7c-e7e3-4743-a0b4-584975425783
-- title:
--   OAI.Generator.Tracial.exists_unitResidual_local_compression_q129: intermediate lemma from OpenAI, Relative generation and the generator problem for finite factors
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.RelativeGeneration.main_theorem` and `OAI.Generator.single_generation_of_II1_separable_predual`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Relative generation and the generator problem for finite factors*, OpenAI Math Release, September 23, 2026, result family 296, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Generator.Tracial.exists_unitResidual_local_compression` of [lean/OAI/Analysis/FactorGeneration/LocalPatches.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/FactorGeneration/LocalPatches.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Generator.Tracial`, with `open scoped BigOperators`, `open UltrapowerBridge`):
--
--   ```lean
--   theorem exists_unitResidual_local_compression_q129
--       (v : PartialUnitary M) (hvN : v.val.val ∈ N)
--       (hsmall : (τ.trace v.support.val).re ≤ 1/4)
--       {ι : Type*} (F : Finset ι) (x : ι → M.toStarSubalgebra) (A B : ι → ℝ)
--       (hAB : ∀ i ∈ F,0 ≤ A i+B i)
--       (hA : ∀ i ∈ F,‖τ.trace (x i)‖ ≤ A i*(τ.trace v.support.val).re)
--       (hB : ∀ i ∈ F,‖τ.trace (star v.val*x i*v.val)‖ ≤ B i*(τ.trace v.support.val).re)
--       (η : ℝ) (hη : 0 < η) :
--       ∃ q : AlgebraProjection M,q ≤ unitResidual v ∧ q.val ≠ 0 ∧ q.val.val ∈ N ∧
--         ∀ i ∈ F,τ.norm₂ (q.val*x i*q.val) < (η+(A i+B i)/3)*τ.norm₂ q.val ∧
--           norm₁ τ (q.val*x i*q.val) < (η+(A i+B i)/3)*(τ.trace q.val).re
--   ```
--
--   **Definitions.** The statement is written with `OAI.Generator.Tracial.AlgebraProjection` and `OAI.Generator.Tracial.algebraProjectionPartialOrder` (definitions bundle `OAIQ129G000` of this split); `OAI.UltrapowerBridge.TracialRepresentation`, `OAI.Generator.Tracial.coordinateInclusion`, `OAI.UltrapowerBridge.TracialRepresentation.norm₂` and `OAI.UltrapowerBridge.TracialRepresentation.trace` (definitions bundle `OAIQ129G001` of this split); `OAI.Generator.Tracial.PartialUnitary`, `OAI.Generator.Tracial.unitResidual` and `OAI.Generator.Tracial.PartialUnitary.val` (definitions bundle `OAIQ129G005` of this split); `OAI.Generator.Tracial.baseVector` (definitions bundle `OAIQ129G008` of this split); `OAI.Generator.Tracial.norm₁` (definitions bundle `OAIQ129G012` of this split).
--
--   **Used by.** The proof of `OAI.Generator.Tracial.exists_finite_partial_independence_q129` of this split imports it.
-- source:
--   OpenAI, Relative generation and the generator problem for finite factors, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 296; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Relative-generation-and-the-generator-problem-for-finite-factors-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/FactorGeneration/LocalPatches.lean (declaration OAI.Generator.Tracial.exists_unitResidual_local_compression)

import Mathlib
import Definitions.Def_OAIQ129G012

section

attribute [-instance] _root_.OAI.Generator.CoefficientOrder.coefficientPartialOrder _root_.OAI.Generator.Tracial.algebraDualNormed _root_.OAI.Generator.Tracial.cyclicPredual_complete _root_.OAI.Generator.Tracial.cyclicPredual_normed _root_.OAI.Generator.Tracial.cyclicPredual_normedSpace _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.Generator.Tracial.functionalSubspaceWeakLocallyConvex _root_.OAI.Generator.Tracial.predualWeakLocallyConvex _root_.OAI.Generator.Tracial.predualWeakScalarTower _root_.OAI.Generator.Tracial.projectionOrbitClosure_complete _root_.OAI.Generator.predualAlgebraDualNormed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] OAI.closedSubmoduleNormedAddCommGroup OAI.closedSubmoduleNormedSpace OAI.closedSubmoduleInner

namespace OAI

noncomputable section

namespace Generator.Tracial

section
open scoped BigOperators
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {N M : VonNeumannAlgebra H} (τ : TracialRepresentation M)

variable (hNM : N ≤ M)
variable (hfactor : ∀ c : N.toStarSubalgebra,
  (∀ a : N.toStarSubalgebra,a*c=c*a) → ∃ z : ℂ,c=z • (1 : N.toStarSubalgebra))
variable (hdiff : ∀ p : N.toStarSubalgebra,IsStarProjection p → p ≠ 0 →
  ∃ q : N.toStarSubalgebra,IsStarProjection q ∧ q ≠ 0 ∧ q ≠ p ∧ p*q=q ∧ q*p=q)
variable (hirr : ∀ c : M.toStarSubalgebra,
  (∀ a : N.toStarSubalgebra,coordinateInclusion hNM a*c=c*coordinateInclusion hNM a) →
  ∃ z : ℂ,c=z • (1 : M.toStarSubalgebra))
variable (hsep : TopologicalSpace.IsSeparable (Set.range (baseVector τ)))
include hfactor hdiff hirr hsep

theorem exists_unitResidual_local_compression_q129
    (v : PartialUnitary M) (hvN : v.val.val ∈ N)
    (hsmall : (τ.trace v.support.val).re ≤ 1/4)
    {ι : Type*} (F : Finset ι) (x : ι → M.toStarSubalgebra) (A B : ι → ℝ)
    (hAB : ∀ i ∈ F,0 ≤ A i+B i)
    (hA : ∀ i ∈ F,‖τ.trace (x i)‖ ≤ A i*(τ.trace v.support.val).re)
    (hB : ∀ i ∈ F,‖τ.trace (star v.val*x i*v.val)‖ ≤ B i*(τ.trace v.support.val).re)
    (η : ℝ) (hη : 0 < η) :
    ∃ q : AlgebraProjection M,q ≤ unitResidual v ∧ q.val ≠ 0 ∧ q.val.val ∈ N ∧
      ∀ i ∈ F,τ.norm₂ (q.val*x i*q.val) < (η+(A i+B i)/3)*τ.norm₂ q.val ∧
        norm₁ τ (q.val*x i*q.val) < (η+(A i+B i)/3)*(τ.trace q.val).re := by
  sorry

end

open UltrapowerBridge

end Generator.Tracial

end

end OAI
end
