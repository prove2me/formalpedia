-- Prove2me | Theorems.Thm_OAI_BoltzmannNonuniqueness_ReferenceGeometry_uniform_damped_finite_block_growth_q80
-- name    : OAI.BoltzmannNonuniqueness.ReferenceGeometry.uniform_damped_finite_block_growth_q80
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-31T19:31:56.143152+00:00
-- url     : https://prove2.me/theorems/78f6538b-d23d-4ae3-a308-b09485ec6f2f
-- title:
--   OAI.BoltzmannNonuniqueness.ReferenceGeometry.uniform_damped_finite_block_growth_q80: intermediate lemma from OpenAI, Nonuniqueness for the periodic hard-sphere Boltzmann equation (result family 363)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.BoltzmannNonuniqueness.nonuniqueness`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Nonuniqueness for the periodic hard-sphere Boltzmann equation (result family 363)*, OpenAI Math Release, September 23, 2026, result family 363, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.BoltzmannNonuniqueness.ReferenceGeometry.uniform_damped_finite_block_growth` of [lean/OAI/MathematicalPhysics/Boltzmann/Branching/ReferenceGrowthBlocks.lean](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/MathematicalPhysics/Boltzmann/Branching/ReferenceGrowthBlocks.lean) at commit 1581d4c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.BoltzmannNonuniqueness.ReferenceGeometry`, with `open MeasureTheory Set ProbabilityTheory Filter`, `open scoped ENNReal NNReal ProbabilityTheory Topology`):
--
--   ```lean
--   theorem uniform_damped_finite_block_growth_q80 {d κ : ℝ}
--       (hd : 0 < d) (hd1 : d ≤ 1) (hκ : 0 < κ) (hκ1 : κ < 1)
--       (hg : (referenceClock : ℝ)*κ < referenceGrowth) :
--       ∃ A₀ : ℝ, 0 < A₀ ∧ ∀ T : ℝ, A₀ ≤ T → ∀ Cmax : ℝ≥0, ∃ N : ℕ,
--         ∀ C : ℝ≥0, referenceClock ≤ C → C ≤ Cmax →
--         ∀ A ∈ Icc A₀ T, ∀ z : FlightState,
--           (7 : ℝ≥0∞) < ∑ j ∈ Finset.range N,
--             eventHistory C (branchingAt C)
--               (flightSeed C ((blockTarget z.1 A κ d).indicator 1)) j (A,z)
--   ```
--
--   **Definitions.** The statement is written with `OAI.BoltzmannNonuniqueness.ReferenceGeometry.V` (definitions bundle `OAIQ080A000` of this split); `OAI.BoltzmannNonuniqueness.ReferenceGeometry.referenceClock` and `OAI.BoltzmannNonuniqueness.ReferenceGeometry.referenceGrowth` (definitions bundle `OAIQ080A001` of this split); `OAI.BoltzmannNonuniqueness.ReferenceGeometry.FlightState`, `OAI.BoltzmannNonuniqueness.ReferenceGeometry.RetainedState`, `OAI.BoltzmannNonuniqueness.ReferenceGeometry.blockTarget`, `OAI.BoltzmannNonuniqueness.ReferenceGeometry.branchingAt`, `OAI.BoltzmannNonuniqueness.ReferenceGeometry.branchingAt_sFinite`, `OAI.BoltzmannNonuniqueness.ReferenceGeometry.eventHistory` and `OAI.BoltzmannNonuniqueness.ReferenceGeometry.flightSeed` (definitions bundle `OAIQ080A002` of this split).
--
--   **Used by.** The proof of `OAI.BoltzmannNonuniqueness.GeometricBackground.geometric_common_block_growth_q80` of this split imports it.
-- source:
--   OpenAI, Nonuniqueness for the periodic hard-sphere Boltzmann equation (result family 363), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 363; paper: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/Nonuniqueness-for-the-periodic-hard-sphere-Boltzmann-equation-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/MathematicalPhysics/Boltzmann/Branching/ReferenceGrowthBlocks.lean (declaration OAI.BoltzmannNonuniqueness.ReferenceGeometry.uniform_damped_finite_block_growth)

import Mathlib
import Definitions.Def_OAIQ080A002

section

attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamPartnerKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedBoundedDensityScaledEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedBoundedPhysicalEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedDensityScaledCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedDensityScaledEventKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedMediumCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedMediumStateCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalPhysicalEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalWindowEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.markedChildKernel_isMarkov _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.mediumCollisionKernel_isSFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.mediumMarkedKernel_isSFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalBeamCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalBeamEvent_pow_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalBeamEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalMarkedCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalMarkedEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalMarkedWord_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalWaitingKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.Compactness.instNonemptyPositivePhaseTest _root_.OAI.BoltzmannNonuniqueness.Compactness.instNonemptySupportedTest
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section

open MeasureTheory Set ProbabilityTheory Filter
open scoped ENNReal NNReal ProbabilityTheory Topology

namespace BoltzmannNonuniqueness.ReferenceGeometry

theorem uniform_damped_finite_block_growth_q80 {d κ : ℝ}
    (hd : 0 < d) (hd1 : d ≤ 1) (hκ : 0 < κ) (hκ1 : κ < 1)
    (hg : (referenceClock : ℝ)*κ < referenceGrowth) :
    ∃ A₀ : ℝ, 0 < A₀ ∧ ∀ T : ℝ, A₀ ≤ T → ∀ Cmax : ℝ≥0, ∃ N : ℕ,
      ∀ C : ℝ≥0, referenceClock ≤ C → C ≤ Cmax →
      ∀ A ∈ Icc A₀ T, ∀ z : FlightState,
        (7 : ℝ≥0∞) < ∑ j ∈ Finset.range N,
          eventHistory C (branchingAt C)
            (flightSeed C ((blockTarget z.1 A κ d).indicator 1)) j (A,z) := by
  sorry

end BoltzmannNonuniqueness.ReferenceGeometry

end

end

end OAI
end
