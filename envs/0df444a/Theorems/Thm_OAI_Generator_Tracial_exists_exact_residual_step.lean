-- Prove2me | Theorems.Thm_OAI_Generator_Tracial_exists_exact_residual_step
-- name    : OAI.Generator.Tracial.exists_exact_residual_step
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-30T12:48:47.549+00:00
-- url     : https://prove2.me/theorems/9d3ddd84-0adc-46a1-a72b-c8c56d90d514
-- title:
--   OAI.Generator.Tracial.exists_exact_residual_step: intermediate lemma from OpenAI, Relative generation and the generator problem for finite factors
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Generator.single_generation_of_II1_separable_predual`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Relative generation and the generator problem for finite factors*, OpenAI Math Release, September 23, 2026, result family 296, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Generator.Tracial.exists_exact_residual_step` of [lean/OAI/Analysis/FactorGeneration/ResidualCompletion.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/FactorGeneration/ResidualCompletion.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Generator.Tracial`, with `open Filter`, `open UltrapowerBridge Filter`):
--
--   ```lean
--   theorem exists_exact_residual_step (ω : Ultrafilter ℕ) (hω : (ω : Filter ℕ) ≤ atTop)
--       (v : ℕ → PartialUnitary M) (hv : ∀ j,(v j).val.val ∈ N)
--       (x : ℕ → Q τ ω) (hx : ∀ i,quotientTrace τ ω (x i)=0)
--       (hm : ExactOrderedMoments τ ω (quotientMap τ (ω : Filter ℕ) (boundedPartialUnitary v)) x) :
--       ∃ u : ℕ → PartialUnitary M,
--         (∀ j,(u j).val.val ∈ N) ∧ (∀ j,v j ≤ u j) ∧
--         ExactOrderedMoments τ ω (quotientMap τ (ω : Filter ℕ) (boundedPartialUnitary u)) x ∧
--         quotientResidualTrace τ ω u ≤ (3/4 : ℝ)*quotientResidualTrace τ ω v
--   ```
--
--   **Definitions.** The statement is written with `OAI.UltrapowerBridge.Bounded`, `OAI.UltrapowerBridge.TracialQuotient`, `OAI.UltrapowerBridge.TracialRepresentation`, `OAI.UltrapowerBridge.quotientMap`, `OAI.UltrapowerBridge.quotientTrace`, `OAI.UltrapowerBridge.traceCongruence` and `OAI.Generator.Tracial.coordinateInclusion` (definitions bundle `OAIQ11Fg000` of this split); `OAI.Generator.Tracial.baseVector` (definitions bundle `OAIQ11Fg003` of this split); `OAI.Generator.Tracial.PartialUnitary` and `OAI.Generator.Tracial.PartialUnitary.val` (definitions bundle `OAIQ11Fg004` of this split); `OAI.Generator.Tracial.Q` and `OAI.Generator.Tracial.boundedPartialUnitary` (definitions bundle `OAIQ11Fg007` of this split); `OAI.Generator.Tracial.PartialUnitary.instPartialOrder` (definitions bundle `OAIQ11Fg012` of this split); `OAI.Generator.Tracial.ExactOrderedMoments` (definitions bundle `OAIQ11Fg014` of this split); `OAI.Generator.Tracial.quotientResidualTrace` (definitions bundle `OAIQ11Fg023` of this split).
--
--   **Used by.** The proof of `OAI.Generator.Tracial.exists_full_support_ordered_independence` of this split imports it.
-- source:
--   OpenAI, Relative generation and the generator problem for finite factors, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 296; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Relative-generation-and-the-generator-problem-for-finite-factors-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/FactorGeneration/ResidualCompletion.lean (declaration OAI.Generator.Tracial.exists_exact_residual_step)

import Mathlib
import Definitions.Def_OAIQ11Fg023

section

attribute [-instance] _root_.OAI.Generator.CoefficientOrder.coefficientPartialOrder _root_.OAI.Generator.Tracial.algebraDualNormed _root_.OAI.Generator.Tracial.cyclicPredual_complete _root_.OAI.Generator.Tracial.cyclicPredual_normed _root_.OAI.Generator.Tracial.cyclicPredual_normedSpace _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.Generator.Tracial.functionalSubspaceWeakLocallyConvex _root_.OAI.Generator.Tracial.predualWeakLocallyConvex _root_.OAI.Generator.Tracial.predualWeakScalarTower _root_.OAI.Generator.Tracial.relativeTraceSpace_complete _root_.OAI.Generator.predualAlgebraDualNormed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] OAI.closedSubmoduleNormedAddCommGroup OAI.closedSubmoduleNormedSpace OAI.closedSubmoduleInner OAI.vonNeumannToStarSubalgebraIsClosed

namespace OAI

noncomputable section

namespace Generator.Tracial

open Filter

section
open UltrapowerBridge Filter
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

theorem exists_exact_residual_step (ω : Ultrafilter ℕ) (hω : (ω : Filter ℕ) ≤ atTop)
    (v : ℕ → PartialUnitary M) (hv : ∀ j,(v j).val.val ∈ N)
    (x : ℕ → Q τ ω) (hx : ∀ i,quotientTrace τ ω (x i)=0)
    (hm : ExactOrderedMoments τ ω (quotientMap τ (ω : Filter ℕ) (boundedPartialUnitary v)) x) :
    ∃ u : ℕ → PartialUnitary M,
      (∀ j,(u j).val.val ∈ N) ∧ (∀ j,v j ≤ u j) ∧
      ExactOrderedMoments τ ω (quotientMap τ (ω : Filter ℕ) (boundedPartialUnitary u)) x ∧
      quotientResidualTrace τ ω u ≤ (3/4 : ℝ)*quotientResidualTrace τ ω v := by
  sorry

end

open UltrapowerBridge Filter
open scoped Topology

end Generator.Tracial

end

end OAI
end
