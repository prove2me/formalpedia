-- Prove2me | Theorems.Thm_OAI_Generator_Tracial_exactOrderedMoments_partial_limit
-- name    : OAI.Generator.Tracial.exactOrderedMoments_partial_limit
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-30T09:55:09.137983+00:00
-- url     : https://prove2.me/theorems/f4673e67-4ca2-47c6-b873-c87d697215aa
-- title:
--   OAI.Generator.Tracial.exactOrderedMoments_partial_limit: intermediate lemma from OpenAI, Relative generation and the generator problem for finite factors
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Generator.single_generation_of_II1_separable_predual`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Relative generation and the generator problem for finite factors*, OpenAI Math Release, September 23, 2026, result family 296, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Generator.Tracial.exactOrderedMoments_partial_limit` of [lean/OAI/Analysis/FactorGeneration/HaarIndependence.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/FactorGeneration/HaarIndependence.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Generator.Tracial`, with `open UltrapowerBridge Filter`, `open scoped Topology`):
--
--   ```lean
--   theorem exactOrderedMoments_partial_limit (a : ℕ → ℕ → PartialUnitary M) (v : Q τ ω)
--       (ha : Tendsto (fun n => quotientMap τ (ω : Filter ℕ) (boundedPartialUnitary (a n))) atTop (𝓝 v))
--       (x : ℕ → Q τ ω)
--       (hm : ∀ n,ExactOrderedMoments τ ω
--         (quotientMap τ (ω : Filter ℕ) (boundedPartialUnitary (a n))) x) :
--       ExactOrderedMoments τ ω v x
--   ```
--
--   **Definitions.** The statement is written with `OAI.UltrapowerBridge.Bounded`, `OAI.UltrapowerBridge.TracialQuotient`, `OAI.UltrapowerBridge.TracialRepresentation`, `OAI.UltrapowerBridge.quotientMap` and `OAI.UltrapowerBridge.traceCongruence` (definitions bundle `OAIQ11Fg000` of this split); `OAI.Generator.Tracial.PartialUnitary` (definitions bundle `OAIQ11Fg004` of this split); `OAI.Generator.Tracial.Q` and `OAI.Generator.Tracial.boundedPartialUnitary` (definitions bundle `OAIQ11Fg007` of this split); `OAI.Generator.Tracial.quotientNormedAddCommGroup` (definitions bundle `OAIQ11Fg011` of this split); `OAI.Generator.Tracial.ExactOrderedMoments` (definitions bundle `OAIQ11Fg014` of this split).
--
--   **Used by.** The proofs of `OAI.Generator.Tracial.exists_coordinate_ordered_unitary` and `OAI_Generator_Tracial_exists_full_support_ordered_independence` of this split import it.
-- source:
--   OpenAI, Relative generation and the generator problem for finite factors, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 296; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Relative-generation-and-the-generator-problem-for-finite-factors-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/FactorGeneration/HaarIndependence.lean (declaration OAI.Generator.Tracial.exactOrderedMoments_partial_limit)

import Mathlib
import Definitions.Def_OAIQ11Fg014

section

attribute [-instance] _root_.OAI.Generator.CoefficientOrder.coefficientPartialOrder _root_.OAI.Generator.Tracial.algebraDualNormed _root_.OAI.Generator.Tracial.cyclicPredual_complete _root_.OAI.Generator.Tracial.cyclicPredual_normed _root_.OAI.Generator.Tracial.cyclicPredual_normedSpace _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.Generator.Tracial.functionalSubspaceWeakLocallyConvex _root_.OAI.Generator.Tracial.predualWeakScalarTower _root_.OAI.Generator.predualAlgebraDualNormed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] OAI.closedSubmoduleNormedAddCommGroup OAI.closedSubmoduleNormedSpace OAI.closedSubmoduleInner OAI.vonNeumannToStarSubalgebraIsClosed

namespace OAI

noncomputable section

namespace Generator.Tracial

section
open UltrapowerBridge Filter
open scoped Topology
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H} (τ : TracialRepresentation M) (ω : Ultrafilter ℕ)

theorem exactOrderedMoments_partial_limit (a : ℕ → ℕ → PartialUnitary M) (v : Q τ ω)
    (ha : Tendsto (fun n => quotientMap τ (ω : Filter ℕ) (boundedPartialUnitary (a n))) atTop (𝓝 v))
    (x : ℕ → Q τ ω)
    (hm : ∀ n,ExactOrderedMoments τ ω
      (quotientMap τ (ω : Filter ℕ) (boundedPartialUnitary (a n))) x) :
    ExactOrderedMoments τ ω v x := by
  sorry

end

open UltrapowerBridge Filter

end Generator.Tracial

end

end OAI
end
