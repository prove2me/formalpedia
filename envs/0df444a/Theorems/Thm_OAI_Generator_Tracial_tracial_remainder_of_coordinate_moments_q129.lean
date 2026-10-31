-- Prove2me | Theorems.Thm_OAI_Generator_Tracial_tracial_remainder_of_coordinate_moments_q129
-- name    : OAI.Generator.Tracial.tracial_remainder_of_coordinate_moments_q129
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-30T21:09:41.446534+00:00
-- url     : https://prove2.me/theorems/887f0a18-75e4-4a23-b206-1d4757e385d8
-- title:
--   OAI.Generator.Tracial.tracial_remainder_of_coordinate_moments_q129: intermediate lemma from OpenAI, Relative generation and the generator problem for finite factors
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.RelativeGeneration.main_theorem` and `OAI.Generator.single_generation_of_II1_separable_predual`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Relative generation and the generator problem for finite factors*, OpenAI Math Release, September 23, 2026, result family 296, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Generator.Tracial.tracial_remainder_of_coordinate_moments` of [lean/OAI/Analysis/FactorGeneration/CoordinatePerturbation.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/FactorGeneration/CoordinatePerturbation.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Generator.Tracial`, with `open Filter`, `open scoped Topology`, `open UltrapowerBridge`):
--
--   ```lean
--   theorem tracial_remainder_of_coordinate_moments_q129 (n : ℕ) (hn : 0 < n)
--       (Φ : MonoidAlgebra ℂ (FreeGroup (PrefixLabel n)) →ₐ[ℂ] Sequences M)
--       (hmom : ∀ g h : FreeGroup (PrefixLabel n),
--         Tendsto (fun k => τ.trace (star (Φ (MonoidAlgebra.single g 1) k)*
--           Φ (MonoidAlgebra.single h 1) k)) (ω : Filter ℕ)
--           (𝓝 (if g = h then 1 else 0)))
--       (α : ℝ) (hα : 0 < α) (hhalf : α < 1/2) :
--       ‖sequenceQuotient τ ω (remainderSequence n α Φ)‖ ≤ 4*α^2/(1-2*α)
--   ```
--
--   **Definitions.** The statement is written with `OAI.Generator.PrefixLabel`, `OAI.UltrapowerBridge.TracialRepresentation`, `OAI.Generator.Tracial.Sequences` and `OAI.UltrapowerBridge.TracialRepresentation.trace` (definitions bundle `OAIQ129G001` of this split); `OAI.UltrapowerBridge.instStarTracialQuotient`, `OAI.UltrapowerBridge.q129Algebra` and `OAI.UltrapowerBridge.q129Semiring` (definitions bundle `OAIQ129G004` of this split); `OAI.Generator.Tracial.Q` (definitions bundle `OAIQ129G008` of this split); `OAI.Generator.Tracial.quotientNormedAddCommGroup` and `OAI.Generator.Tracial.sequenceQuotient` (definitions bundle `OAIQ129G011` of this split); `OAI.Generator.Tracial.remainderSequence` (definitions bundle `OAIQ129G014` of this split).
--
--   **Used by.** The proof of `OAI.Generator.Tracial.SuccessiveCoordinateHaar.exponential_product_correlation_q129` of this split imports it.
-- source:
--   OpenAI, Relative generation and the generator problem for finite factors, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 296; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Relative-generation-and-the-generator-problem-for-finite-factors-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/FactorGeneration/CoordinatePerturbation.lean (declaration OAI.Generator.Tracial.tracial_remainder_of_coordinate_moments)

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_OAIQ129G014

section

attribute [-instance] _root_.OAI.Generator.Tracial.algebraDualNormed _root_.OAI.Generator.Tracial.cyclicPredual_complete _root_.OAI.Generator.Tracial.cyclicPredual_normed _root_.OAI.Generator.Tracial.cyclicPredual_normedSpace _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.Generator.Tracial.functionalSubspaceWeakLocallyConvex _root_.OAI.Generator.Tracial.predualWeakLocallyConvex _root_.OAI.Generator.Tracial.predualWeakScalarTower _root_.OAI.Generator.Tracial.projectionOrbitClosure_complete _root_.OAI.Generator.Tracial.relativeTraceSpace_complete _root_.OAI.Generator.predualAlgebraDualNormed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] OAI.closedSubmoduleNormedAddCommGroup OAI.closedSubmoduleNormedSpace OAI.closedSubmoduleInner

namespace OAI

noncomputable section

namespace Generator.Tracial

section

open Filter
open scoped Topology
attribute [local instance] Classical.propDecidable Classical.decEq
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H} (τ : TracialRepresentation M) (ω : Ultrafilter ℕ)

theorem tracial_remainder_of_coordinate_moments_q129 (n : ℕ) (hn : 0 < n)
    (Φ : MonoidAlgebra ℂ (FreeGroup (PrefixLabel n)) →ₐ[ℂ] Sequences M)
    (hmom : ∀ g h : FreeGroup (PrefixLabel n),
      Tendsto (fun k => τ.trace (star (Φ (MonoidAlgebra.single g 1) k)*
        Φ (MonoidAlgebra.single h 1) k)) (ω : Filter ℕ)
        (𝓝 (if g = h then 1 else 0)))
    (α : ℝ) (hα : 0 < α) (hhalf : α < 1/2) :
    ‖sequenceQuotient τ ω (remainderSequence n α Φ)‖ ≤ 4*α^2/(1-2*α) := by
  sorry

end

attribute [local instance] Classical.propDecidable Classical.decEq
open UltrapowerBridge
open scoped BigOperators

end Generator.Tracial

end

end OAI
end
