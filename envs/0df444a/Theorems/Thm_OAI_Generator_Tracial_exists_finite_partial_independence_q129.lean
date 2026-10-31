-- Prove2me | Theorems.Thm_OAI_Generator_Tracial_exists_finite_partial_independence_q129
-- name    : OAI.Generator.Tracial.exists_finite_partial_independence_q129
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-30T20:37:07.53762+00:00
-- url     : https://prove2.me/theorems/4ac610b7-47c5-4e60-9904-0443289205c0
-- title:
--   OAI.Generator.Tracial.exists_finite_partial_independence_q129: intermediate lemma from OpenAI, Relative generation and the generator problem for finite factors
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.RelativeGeneration.main_theorem` and `OAI.Generator.single_generation_of_II1_separable_predual`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Relative generation and the generator problem for finite factors*, OpenAI Math Release, September 23, 2026, result family 296, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Generator.Tracial.exists_finite_partial_independence` of [lean/OAI/Analysis/FactorGeneration/HaarPatches.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/FactorGeneration/HaarPatches.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Generator.Tracial`, with `open UltrapowerBridge`):
--
--   ```lean
--   theorem exists_finite_partial_independence_q129
--       (F : Finset M.toStarSubalgebra) (hF : ∀ x ∈ F,‖x‖ ≤ 1)
--       (hcenter : ∀ x ∈ F,τ.trace x=0) (n : ℕ) (ε : ℝ) (hε : 0 < ε) :
--       ∃ v : PartialUnitary M,v.val.val ∈ N ∧ 1/4 < (τ.trace v.support.val).re ∧
--         ∀ x₀ ∈ (F : Set M.toStarSubalgebra) ∪ {1},∀ xs : List (Bool × M.toStarSubalgebra),
--           1 ≤ xs.length → xs.length ≤ n → patchingCoefficients (F : Set M.toStarSubalgebra) xs →
--           ‖τ.trace (x₀*patchingWord v.val xs)‖ ≤ ε
--   ```
--
--   **Definitions.** The statement is written with `OAI.UltrapowerBridge.TracialRepresentation`, `OAI.Generator.Tracial.coordinateInclusion`, `OAI.Generator.Tracial.patchingCoefficients`, `OAI.Generator.Tracial.patchingWord` and `OAI.UltrapowerBridge.TracialRepresentation.trace` (definitions bundle `OAIQ129G001` of this split); `OAI.Generator.Tracial.PartialUnitary` and `OAI.Generator.Tracial.PartialUnitary.val` (definitions bundle `OAIQ129G005` of this split); `OAI.Generator.Tracial.baseVector` (definitions bundle `OAIQ129G008` of this split).
--
--   **Used by.** The proofs of `OAI.Generator.Tracial.exists_exact_residual_iteration_q129` and `OAI_Generator_Tracial_exists_quotient_corner_partial_sequence_q129` of this split import it.
-- source:
--   OpenAI, Relative generation and the generator problem for finite factors, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 296; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Relative-generation-and-the-generator-problem-for-finite-factors-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/FactorGeneration/HaarPatches.lean (declaration OAI.Generator.Tracial.exists_finite_partial_independence)

import Mathlib
import Definitions.Def_OAIQ129G008

section

attribute [-instance] _root_.OAI.Generator.CoefficientOrder.coefficientPartialOrder _root_.OAI.Generator.Tracial.algebraDualNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.Generator.Tracial.functionalSubspaceWeakLocallyConvex _root_.OAI.Generator.Tracial.projectionOrbitClosure_complete _root_.OAI.Generator.predualAlgebraDualNormed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] OAI.closedSubmoduleNormedAddCommGroup OAI.closedSubmoduleNormedSpace OAI.closedSubmoduleInner

namespace OAI

noncomputable section

namespace Generator.Tracial

section
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

theorem exists_finite_partial_independence_q129
    (F : Finset M.toStarSubalgebra) (hF : ∀ x ∈ F,‖x‖ ≤ 1)
    (hcenter : ∀ x ∈ F,τ.trace x=0) (n : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ v : PartialUnitary M,v.val.val ∈ N ∧ 1/4 < (τ.trace v.support.val).re ∧
      ∀ x₀ ∈ (F : Set M.toStarSubalgebra) ∪ {1},∀ xs : List (Bool × M.toStarSubalgebra),
        1 ≤ xs.length → xs.length ≤ n → patchingCoefficients (F : Set M.toStarSubalgebra) xs →
        ‖τ.trace (x₀*patchingWord v.val xs)‖ ≤ ε := by
  sorry

end

open Filter
open scoped Topology

open Filter
open scoped Topology

end Generator.Tracial

end

end OAI
end
