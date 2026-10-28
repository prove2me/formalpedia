-- Prove2me | Theorems.Thm_OAI_FiniteFactor_sourceSamplingTrimmed_marginals_event
-- name    : OAI.FiniteFactor.sourceSamplingTrimmed_marginals_event
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-25T23:38:03.931098+00:00
-- url     : https://prove2.me/theorems/80fbe6e1-bb6d-482a-8148-5a18e9429194
-- title:
--   OAI.FiniteFactor.sourceSamplingTrimmed_marginals_event: intermediate lemma from OpenAI, Invariant-projection counterexamples for every irrational rotation
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.FiniteFactor.main_theorem`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Invariant-projection counterexamples for every irrational rotation*, OpenAI Math Release, September 27, 2026, result family 293, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.FiniteFactor.sourceSamplingTrimmed_marginals_event` of [lean/OAI/Analysis/FiniteFactor/OrbitSampling/TrimmedMarginals.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/FiniteFactor/OrbitSampling/TrimmedMarginals.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.FiniteFactor`, with `open MeasureTheory Filter Finset`, `open scoped Classical ENNReal Topology`):
--
--   ```lean
--   theorem sourceSamplingTrimmed_marginals_event : ∀ᵐ θ ∂sourceAngleLaw,
--       ∀ (I : Finset SourceCoordinate) (r : Bool), ∃ C : ℝ, ∀ s : ℕ,
--         ∃ g : (SourceCoordinate → ℝ) → ℝ,
--           Measurable g ∧ (∀ x, 0 ≤ g x) ∧
--           (sourceSamplingTrimmed I s θ).map (sourceSamplingEndpoint r) =
--             sourceSamplingHaar.withDensity (fun x => ENNReal.ofReal (g x)) ∧
--           MemLp g 2 sourceSamplingHaar ∧ (∫ x, g x^2 ∂sourceSamplingHaar) ≤ C
--   ```
--
--   **Definitions.** The statement is written with `OAI.FiniteFactor.SourceCoordinate`, `OAI.FiniteFactor.sourceAngleLaw`, `OAI.FiniteFactor.sourceSamplingHaar` and `OAI.FiniteFactor.sourceSamplingTrimmed` (definitions bundle `OAIQ3Ff000` of this split); `OAI.FiniteFactor.sourceSamplingEndpoint` (definitions bundle `OAIQ3Ff002` of this split).
--
--   **Used by.** The proof of `OAI.FiniteFactor.exists_source_prepared_finite` of this split imports it.
-- source:
--   OpenAI, Invariant-projection counterexamples for every irrational rotation, OpenAI Math Release, September 27, 2026, https://github.com/openai/math (result family 293; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Invariant-projection-counterexamples-for-every-irrational-rotation-September-27-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/FiniteFactor/OrbitSampling/TrimmedMarginals.lean (declaration OAI.FiniteFactor.sourceSamplingTrimmed_marginals_event)

import Mathlib
import Definitions.Def_OAIQ3Ff002

section

attribute [-instance] _root_.OAI.FiniteFactor.sourceBiasedRealMeasure_probability _root_.OAI.FiniteFactor.sourceFiniteReferenceKernel_markov _root_.OAI.FiniteFactor.sourceHilbert_separable _root_.OAI.FiniteFactor.sourceNormalFunctionalSpace_complete _root_.OAI.FiniteFactor.sourceNormalPredualSpace_complete _root_.OAI.FiniteFactor.sourceNormalPredualSpace_normedGroup _root_.OAI.FiniteFactor.sourceNormalPredualSpace_normedSpace _root_.OAI.FiniteFactor.sourceResamplingKernel_markov _root_.OAI.FiniteFactor.sourceSamplingTorus_borel _root_.OAI.FiniteFactor.sourceSamplingTorus_compact _root_.OAI.FiniteFactor.sourceUnitCircle_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FiniteFactor
open MeasureTheory Filter Finset
open scoped Classical ENNReal Topology
noncomputable section

theorem sourceSamplingTrimmed_marginals_event : ∀ᵐ θ ∂sourceAngleLaw,
    ∀ (I : Finset SourceCoordinate) (r : Bool), ∃ C : ℝ, ∀ s : ℕ,
      ∃ g : (SourceCoordinate → ℝ) → ℝ,
        Measurable g ∧ (∀ x, 0 ≤ g x) ∧
        (sourceSamplingTrimmed I s θ).map (sourceSamplingEndpoint r) =
          sourceSamplingHaar.withDensity (fun x => ENNReal.ofReal (g x)) ∧
        MemLp g 2 sourceSamplingHaar ∧ (∫ x, g x^2 ∂sourceSamplingHaar) ≤ C := by
  sorry

end
end FiniteFactor

end OAI
end
