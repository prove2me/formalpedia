-- Prove2me | Theorems.Thm_OAI_BoltzmannNonuniqueness_PeriodicApproximation_exists_global_density_pair_with_strong_mass_q80
-- name    : OAI.BoltzmannNonuniqueness.PeriodicApproximation.exists_global_density_pair_with_strong_mass_q80
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-31T19:31:58.622322+00:00
-- url     : https://prove2.me/theorems/c1c30d10-428d-47d3-a5fa-f9f9199cda29
-- title:
--   OAI.BoltzmannNonuniqueness.PeriodicApproximation.exists_global_density_pair_with_strong_mass_q80 (OpenAI intermediate lemma)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.BoltzmannNonuniqueness.nonuniqueness`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Nonuniqueness for the periodic hard-sphere Boltzmann equation (result family 363)*, OpenAI Math Release, September 23, 2026, result family 363, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.BoltzmannNonuniqueness.PeriodicApproximation.exists_global_density_pair_with_strong_mass` of [lean/OAI/MathematicalPhysics/Boltzmann/Compactness/PeriodicJointBudgetLimit.lean](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/MathematicalPhysics/Boltzmann/Compactness/PeriodicJointBudgetLimit.lean) at commit 1581d4c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.BoltzmannNonuniqueness.PeriodicApproximation`, with `open MeasureTheory Set Filter`, `open scoped ENNReal Topology`):
--
--   ```lean
--   theorem exists_global_density_pair_with_strong_mass_q80
--       (f : Density) (hfm : Measurable f) (hf : ∀ p, 0 ≤ f p) (hi : Integrable (entropyMoment f))
--       (χ : ℕ → Published.SpaceTime → ℝ)
--       (hχ : ∀ j, ContDiff ℝ (⊤ : ℕ∞) (χ j)) (hχc : ∀ j, HasCompactSupport (χ j))
--       (hχs : ∀ j, tsupport (χ j) ⊆ TorusKineticChart.interiorRegion)
--       (ψ : ℕ → Velocity → ℝ)
--       (hψ : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (ψ i)) (hψc : ∀ i, HasCompactSupport (ψ i)) :
--       ∃ (G : GlobalWeakLimit f hfm) (W : (ℝ × Position) × (Velocity × Velocity) → ℝ),
--         Published.WeakL1Converges
--           ((finiteTimeMeasure.prod (volume : Measure Position)).prod (volume.prod volume))
--           (fun n => Compactness.normalizedPair volume
--             (approximatingSolution f hfm (G.indices n)).kineticProfile) W ∧
--         (∀ s i, Tendsto (fun n => eLpNorm (fun z =>
--           χ s z*(∫ v, ψ i v*TorusKineticChart.liftDensity
--             (approximatingSolution f hfm (G.indices n)).kineticProfile (z,v))-
--           χ s z*(∫ v, ψ i v*TorusKineticChart.liftDensity G.kineticProfile (z,v))) 1 volume)
--           atTop (𝓝 0)) ∧
--         (∀ s, Tendsto (fun n => eLpNorm (fun z =>
--           χ s z*(∫ v, TorusKineticChart.liftDensity
--             (approximatingSolution f hfm (G.indices n)).kineticProfile (z,v))-
--           χ s z*(∫ v, TorusKineticChart.liftDensity G.kineticProfile (z,v))) 1 volume)
--           atTop (𝓝 0))
--   ```
--
--   **Definitions.** The statement is written with `OAI.BoltzmannNonuniqueness.Compactness.normalizedPair`, `OAI.BoltzmannNonuniqueness.PeriodicApproximation.finiteTimeMeasure`, `OAI.BoltzmannNonuniqueness.PeriodicApproximation.initialApproximation`, `OAI.BoltzmannNonuniqueness.Published.SpaceTime`, `OAI.BoltzmannNonuniqueness.Published.Velocity`, `OAI.BoltzmannNonuniqueness.Published.WeakL1Converges` and `OAI.BoltzmannNonuniqueness.PeriodicApproximation.BoundedCutoffSolution.kineticProfile` (definitions bundle `OAIQ080A000` of this split); `OAI.BoltzmannNonuniqueness.PeriodicApproximation.GlobalWeakLimit`, `OAI.BoltzmannNonuniqueness.PeriodicApproximation.approximatingSolution`, `OAI.BoltzmannNonuniqueness.TorusKineticChart.interiorRegion`, `OAI.BoltzmannNonuniqueness.TorusKineticChart.liftDensity` and `OAI.BoltzmannNonuniqueness.PeriodicApproximation.GlobalWeakLimit.kineticProfile` (definitions bundle `OAIQ080A002` of this split); `OAI.BoltzmannNonuniqueness.Density`, `OAI.BoltzmannNonuniqueness.Phase`, `OAI.BoltzmannNonuniqueness.Position`, `OAI.BoltzmannNonuniqueness.Velocity` and `OAI.BoltzmannNonuniqueness.entropyMoment` (the published bundle `Def_BoltzmannNonuniqueness`).
--
--   **Used by.** The proof of `OAI.BoltzmannNonuniqueness.PeriodicApproximation.exists_globalCollisionLimit_q80` of this split imports it.
-- source:
--   OpenAI, Nonuniqueness for the periodic hard-sphere Boltzmann equation (result family 363), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 363; paper: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/Nonuniqueness-for-the-periodic-hard-sphere-Boltzmann-equation-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/MathematicalPhysics/Boltzmann/Compactness/PeriodicJointBudgetLimit.lean (declaration OAI.BoltzmannNonuniqueness.PeriodicApproximation.exists_global_density_pair_with_strong_mass)

import Mathlib
import Definitions.Def_BoltzmannNonuniqueness
import Definitions.Def_OAIQ080A002

section

attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.characteristicGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.retainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.awayOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.nearOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalRetainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.densityScaledCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalBeamKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalPhysicalEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalWindowEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalEventMeasure_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.scaledBeamNormalKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseEndpointKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseSeed_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.residenceKernel_sFinite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal Topology
namespace BoltzmannNonuniqueness.PeriodicApproximation

theorem exists_global_density_pair_with_strong_mass_q80
    (f : Density) (hfm : Measurable f) (hf : ∀ p, 0 ≤ f p) (hi : Integrable (entropyMoment f))
    (χ : ℕ → Published.SpaceTime → ℝ)
    (hχ : ∀ j, ContDiff ℝ (⊤ : ℕ∞) (χ j)) (hχc : ∀ j, HasCompactSupport (χ j))
    (hχs : ∀ j, tsupport (χ j) ⊆ TorusKineticChart.interiorRegion)
    (ψ : ℕ → Velocity → ℝ)
    (hψ : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (ψ i)) (hψc : ∀ i, HasCompactSupport (ψ i)) :
    ∃ (G : GlobalWeakLimit f hfm) (W : (ℝ × Position) × (Velocity × Velocity) → ℝ),
      Published.WeakL1Converges
        ((finiteTimeMeasure.prod (volume : Measure Position)).prod (volume.prod volume))
        (fun n => Compactness.normalizedPair volume
          (approximatingSolution f hfm (G.indices n)).kineticProfile) W ∧
      (∀ s i, Tendsto (fun n => eLpNorm (fun z =>
        χ s z*(∫ v, ψ i v*TorusKineticChart.liftDensity
          (approximatingSolution f hfm (G.indices n)).kineticProfile (z,v))-
        χ s z*(∫ v, ψ i v*TorusKineticChart.liftDensity G.kineticProfile (z,v))) 1 volume)
        atTop (𝓝 0)) ∧
      (∀ s, Tendsto (fun n => eLpNorm (fun z =>
        χ s z*(∫ v, TorusKineticChart.liftDensity
          (approximatingSolution f hfm (G.indices n)).kineticProfile (z,v))-
        χ s z*(∫ v, TorusKineticChart.liftDensity G.kineticProfile (z,v))) 1 volume)
        atTop (𝓝 0)) := by
  sorry

end BoltzmannNonuniqueness.PeriodicApproximation

end

end

end OAI
end
