-- Prove2me | Theorems.Thm_OAI_Generator_Tracial_nonempty_successiveCoordinateHaar_q129
-- name    : OAI.Generator.Tracial.nonempty_successiveCoordinateHaar_q129
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-30T20:56:03.327978+00:00
-- url     : https://prove2.me/theorems/df35e94b-5623-4241-bd8a-7365c07ee8b9
-- title:
--   OAI.Generator.Tracial.nonempty_successiveCoordinateHaar_q129: intermediate lemma from OpenAI, Relative generation and the generator problem for finite factors
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.RelativeGeneration.main_theorem` and `OAI.Generator.single_generation_of_II1_separable_predual`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Relative generation and the generator problem for finite factors*, OpenAI Math Release, September 23, 2026, result family 296, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Generator.Tracial.nonempty_successiveCoordinateHaar` of [lean/OAI/Analysis/FactorGeneration/HaarSequences.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/FactorGeneration/HaarSequences.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Generator.Tracial`, with `open UltrapowerBridge Filter`):
--
--   ```lean
--   theorem nonempty_successiveCoordinateHaar_q129 (hω : (ω : Filter ℕ) ≤ atTop)
--       (seed : Set (Q τ ω)) (hseed : seed.Countable) :
--       Nonempty (SuccessiveCoordinateHaar τ ω hNM seed)
--   ```
--
--   **Definitions.** The statement is written with `OAI.UltrapowerBridge.TracialRepresentation` and `OAI.Generator.Tracial.coordinateInclusion` (definitions bundle `OAIQ129G001` of this split); `OAI.Generator.Tracial.Q` and `OAI.Generator.Tracial.baseVector` (definitions bundle `OAIQ129G008` of this split); `OAI.Generator.Tracial.SuccessiveCoordinateHaar` (definitions bundle `OAIQ129G011` of this split).
--
--   **Used by.** The proof of `OAI.Generator.Tracial.represented_relative_generation_q129` of this split imports it.
-- source:
--   OpenAI, Relative generation and the generator problem for finite factors, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 296; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Relative-generation-and-the-generator-problem-for-finite-factors-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/FactorGeneration/HaarSequences.lean (declaration OAI.Generator.Tracial.nonempty_successiveCoordinateHaar)

import Mathlib
import Definitions.Def_OAIQ129G011

section

attribute [-instance] _root_.OAI.Generator.CoefficientOrder.coefficientPartialOrder _root_.OAI.Generator.Tracial.algebraDualNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.Generator.Tracial.functionalSubspaceWeakLocallyConvex _root_.OAI.Generator.predualAlgebraDualNormed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] OAI.closedSubmoduleNormedAddCommGroup OAI.closedSubmoduleNormedSpace OAI.closedSubmoduleInner

namespace OAI

noncomputable section

namespace Generator.Tracial

section
open UltrapowerBridge Filter
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {N M : VonNeumannAlgebra H} (τ : TracialRepresentation M) (ω : Ultrafilter ℕ)

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

theorem nonempty_successiveCoordinateHaar_q129 (hω : (ω : Filter ℕ) ≤ atTop)
    (seed : Set (Q τ ω)) (hseed : seed.Countable) :
    Nonempty (SuccessiveCoordinateHaar τ ω hNM seed) := by
  sorry

end

open UltrapowerBridge Filter

end Generator.Tracial

end

end OAI
end
