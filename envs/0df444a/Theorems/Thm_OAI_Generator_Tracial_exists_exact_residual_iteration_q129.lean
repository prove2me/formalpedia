-- Prove2me | Theorems.Thm_OAI_Generator_Tracial_exists_exact_residual_iteration_q129
-- name    : OAI.Generator.Tracial.exists_exact_residual_iteration_q129
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-30T21:16:40.275752+00:00
-- url     : https://prove2.me/theorems/a73eeddf-1529-4332-9069-01a960dd9273
-- title:
--   OAI.Generator.Tracial.exists_exact_residual_iteration_q129: intermediate lemma from OpenAI, Relative generation and the generator problem for finite factors
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.RelativeGeneration.main_theorem` and `OAI.Generator.single_generation_of_II1_separable_predual`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Relative generation and the generator problem for finite factors*, OpenAI Math Release, September 23, 2026, result family 296, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Generator.Tracial.exists_exact_residual_iteration` of [lean/OAI/Analysis/FactorGeneration/ResidualCompletion.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/FactorGeneration/ResidualCompletion.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Generator.Tracial`, with `open Filter`, `open UltrapowerBridge Filter`):
--
--   ```lean
--   theorem exists_exact_residual_iteration_q129 (ω : Ultrafilter ℕ) (hω : (ω : Filter ℕ) ≤ atTop)
--       (v : ℕ → PartialUnitary M) (hv : ∀ j,(v j).val.val ∈ N)
--       (x : ℕ → Q τ ω) (hx : ∀ i,quotientTrace τ ω (x i)=0)
--       (hm : ExactOrderedMoments τ ω (quotientMap τ (ω : Filter ℕ) (boundedPartialUnitary v)) x) :
--       ∃ a : ℕ → ℕ → PartialUnitary M,a 0=v ∧
--         (∀ n j,(a n j).val.val ∈ N) ∧ (∀ j,Monotone (fun n => a n j)) ∧
--         (∀ n,ExactOrderedMoments τ ω (quotientMap τ (ω : Filter ℕ) (boundedPartialUnitary (a n))) x) ∧
--         ∀ n,quotientResidualTrace τ ω (a n) ≤ (3/4 : ℝ)^n*quotientResidualTrace τ ω v
--   ```
--
--   **Definitions.** The statement is written with `OAI.UltrapowerBridge.Bounded`, `OAI.UltrapowerBridge.TracialRepresentation` and `OAI.Generator.Tracial.coordinateInclusion` (definitions bundle `OAIQ129G001` of this split); `OAI.UltrapowerBridge.TracialQuotient`, `OAI.UltrapowerBridge.quotientMap`, `OAI.UltrapowerBridge.quotientTrace` and `OAI.UltrapowerBridge.traceCongruence` (definitions bundle `OAIQ129G004` of this split); `OAI.Generator.Tracial.PartialUnitary`, `OAI.Generator.Tracial.PartialUnitary.instPartialOrder` and `OAI.Generator.Tracial.PartialUnitary.val` (definitions bundle `OAIQ129G005` of this split); `OAI.Generator.Tracial.Q` and `OAI.Generator.Tracial.baseVector` (definitions bundle `OAIQ129G008` of this split); `OAI.Generator.Tracial.ExactOrderedMoments` and `OAI.Generator.Tracial.boundedPartialUnitary` (definitions bundle `OAIQ129G011` of this split); `OAI.Generator.Tracial.quotientResidualTrace` (definitions bundle `OAIQ129G014` of this split).
--
--   **Used by.** The proof of `OAI.Generator.Tracial.exists_coordinate_ordered_unitary_q129` of this split imports it.
-- source:
--   OpenAI, Relative generation and the generator problem for finite factors, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 296; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Relative-generation-and-the-generator-problem-for-finite-factors-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/FactorGeneration/ResidualCompletion.lean (declaration OAI.Generator.Tracial.exists_exact_residual_iteration)

import Mathlib
import Definitions.Def_OAIQ129G014

section

attribute [-instance] _root_.OAI.Generator.CoefficientOrder.coefficientPartialOrder _root_.OAI.Generator.Tracial.algebraDualNormed _root_.OAI.Generator.Tracial.cyclicPredual_complete _root_.OAI.Generator.Tracial.cyclicPredual_normed _root_.OAI.Generator.Tracial.cyclicPredual_normedSpace _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.Generator.Tracial.functionalSubspaceWeakLocallyConvex _root_.OAI.Generator.Tracial.predualWeakLocallyConvex _root_.OAI.Generator.Tracial.predualWeakScalarTower _root_.OAI.Generator.Tracial.relativeTraceSpace_complete _root_.OAI.Generator.predualAlgebraDualNormed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] OAI.closedSubmoduleNormedAddCommGroup OAI.closedSubmoduleNormedSpace OAI.closedSubmoduleInner

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

theorem exists_exact_residual_iteration_q129 (ω : Ultrafilter ℕ) (hω : (ω : Filter ℕ) ≤ atTop)
    (v : ℕ → PartialUnitary M) (hv : ∀ j,(v j).val.val ∈ N)
    (x : ℕ → Q τ ω) (hx : ∀ i,quotientTrace τ ω (x i)=0)
    (hm : ExactOrderedMoments τ ω (quotientMap τ (ω : Filter ℕ) (boundedPartialUnitary v)) x) :
    ∃ a : ℕ → ℕ → PartialUnitary M,a 0=v ∧
      (∀ n j,(a n j).val.val ∈ N) ∧ (∀ j,Monotone (fun n => a n j)) ∧
      (∀ n,ExactOrderedMoments τ ω (quotientMap τ (ω : Filter ℕ) (boundedPartialUnitary (a n))) x) ∧
      ∀ n,quotientResidualTrace τ ω (a n) ≤ (3/4 : ℝ)^n*quotientResidualTrace τ ω v := by
  sorry

end

open UltrapowerBridge Filter
open scoped Topology

end Generator.Tracial

end

end OAI
end
