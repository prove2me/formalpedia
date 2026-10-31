-- Prove2me | Theorems.Thm_OAI_Generator_Tracial_exists_supported_corner_partial_sequence
-- name    : OAI.Generator.Tracial.exists_supported_corner_partial_sequence
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-30T09:42:20.432632+00:00
-- url     : https://prove2.me/theorems/23c5d0a1-46da-49da-b16b-2028128d3771
-- title:
--   OAI.Generator.Tracial.exists_supported_corner_partial_sequence: intermediate lemma from OpenAI, Relative generation and the generator problem for finite factors
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Generator.single_generation_of_II1_separable_predual`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Relative generation and the generator problem for finite factors*, OpenAI Math Release, September 23, 2026, result family 296, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Generator.Tracial.exists_supported_corner_partial_sequence` of [lean/OAI/Analysis/FactorGeneration/CornerIndependence.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/FactorGeneration/CornerIndependence.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Generator.Tracial`, with `open Filter`, `open scoped Topology`, `open Filter`, `open scoped Topology`, `open UltrapowerBridge`):
--
--   ```lean
--   theorem exists_supported_corner_partial_sequence
--       (p : ℕ → AlgebraProjection M) (hpN : ∀ j,(p j).val.val ∈ N)
--       (hp : ∀ j,(p j).val ≠ 0)
--       (x : ℕ → ℕ → M.toStarSubalgebra) (hx : ∀ i j,‖x i j‖ ≤ 1)
--       (hc : ∀ i j,τ.trace (x i j)=0)
--       (hl : ∀ i j,(p j).val*x i j=x i j) (hr : ∀ i j,x i j*(p j).val=x i j) :
--       ∃ v : ℕ → PartialUnitary M,
--         (∀ j,(v j).val.val ∈ N) ∧ (∀ j,(v j).support ≤ p j) ∧
--         (∀ j,(τ.trace (p j).val).re/4 < (τ.trace (v j).support.val).re) ∧
--         ∀ first last : Option ℕ,∀ xs : List (Bool × ℕ),∀ s : Bool,
--           Tendsto (fun j => τ.trace (indexedCoefficient x j first *
--             patchingWord (v j).val (xs.map (fun a => (a.1,x a.2 j)) ++
--               [(s,indexedCoefficient x j last)]))) atTop (𝓝 0)
--   ```
--
--   **Definitions.** The statement is written with `OAI.UltrapowerBridge.TracialRepresentation`, `OAI.Generator.Tracial.coordinateInclusion` and `OAI.UltrapowerBridge.TracialRepresentation.trace` (definitions bundle `OAIQ11Fg000` of this split); `OAI.Generator.Tracial.AlgebraProjection` and `OAI.Generator.Tracial.algebraProjectionPartialOrder` (definitions bundle `OAIQ11Fg001` of this split); `OAI.Generator.Tracial.indexedCoefficient` and `OAI.Generator.Tracial.patchingWord` (definitions bundle `OAIQ11Fg002` of this split); `OAI.Generator.Tracial.baseVector` (definitions bundle `OAIQ11Fg003` of this split); `OAI.Generator.Tracial.PartialUnitary` and `OAI.Generator.Tracial.PartialUnitary.val` (definitions bundle `OAIQ11Fg004` of this split).
--
--   **Used by.** The proofs of `OAI_Generator_Tracial_exists_quotient_corner_partial_sequence` and `OAI.Generator.Tracial.exists_residual_quotient_increment` of this split import it.
-- source:
--   OpenAI, Relative generation and the generator problem for finite factors, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 296; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Relative-generation-and-the-generator-problem-for-finite-factors-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/FactorGeneration/CornerIndependence.lean (declaration OAI.Generator.Tracial.exists_supported_corner_partial_sequence)

import Mathlib
import Definitions.Def_OAIQ11Fg003
import Definitions.Def_OAIQ11Fg004

section

attribute [-instance] _root_.OAI.Generator.CoefficientOrder.coefficientPartialOrder _root_.OAI.Generator.Tracial.algebraDualNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.Generator.Tracial.functionalSubspaceWeakLocallyConvex _root_.OAI.Generator.Tracial.projectionOrbitClosure_complete _root_.OAI.Generator.predualAlgebraDualNormed _root_.OAI.Generator.predualFunctionals_normed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] OAI.closedSubmoduleNormedAddCommGroup OAI.closedSubmoduleNormedSpace OAI.closedSubmoduleInner OAI.vonNeumannToStarSubalgebraIsClosed

namespace OAI

noncomputable section

namespace Generator.Tracial

open Filter
open scoped Topology

open Filter
open scoped Topology
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

theorem exists_supported_corner_partial_sequence
    (p : ℕ → AlgebraProjection M) (hpN : ∀ j,(p j).val.val ∈ N)
    (hp : ∀ j,(p j).val ≠ 0)
    (x : ℕ → ℕ → M.toStarSubalgebra) (hx : ∀ i j,‖x i j‖ ≤ 1)
    (hc : ∀ i j,τ.trace (x i j)=0)
    (hl : ∀ i j,(p j).val*x i j=x i j) (hr : ∀ i j,x i j*(p j).val=x i j) :
    ∃ v : ℕ → PartialUnitary M,
      (∀ j,(v j).val.val ∈ N) ∧ (∀ j,(v j).support ≤ p j) ∧
      (∀ j,(τ.trace (p j).val).re/4 < (τ.trace (v j).support.val).re) ∧
      ∀ first last : Option ℕ,∀ xs : List (Bool × ℕ),∀ s : Bool,
        Tendsto (fun j => τ.trace (indexedCoefficient x j first *
          patchingWord (v j).val (xs.map (fun a => (a.1,x a.2 j)) ++
            [(s,indexedCoefficient x j last)]))) atTop (𝓝 0) := by
  sorry

end Generator.Tracial

end

end OAI
end
