-- Prove2me | Theorems.Thm_OAI_BoltzmannNonuniqueness_PeriodicApproximation_approximatingSolution_renormalized_average_compactness_q80
-- name    : OAI.BoltzmannNonuniqueness.PeriodicApproximation.approximatingSolution_renormalized_average_compactness_q80
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-31T19:31:24.48841+00:00
-- url     : https://prove2.me/theorems/234f135c-217c-49cb-9ce2-ec08caa6eb57
-- title:
--   OAI.BoltzmannNonuniqueness.PeriodicApproximation.approximatingSolution_renormalized_average_compactness_q80 (OpenAI intermediate lemma)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.BoltzmannNonuniqueness.nonuniqueness`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Nonuniqueness for the periodic hard-sphere Boltzmann equation (result family 363)*, OpenAI Math Release, September 23, 2026, result family 363, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.BoltzmannNonuniqueness.PeriodicApproximation.approximatingSolution_renormalized_average_compactness` of [lean/OAI/MathematicalPhysics/Boltzmann/Compactness/PeriodicWeakCompactness.lean](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/MathematicalPhysics/Boltzmann/Compactness/PeriodicWeakCompactness.lean) at commit 1581d4c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.BoltzmannNonuniqueness.PeriodicApproximation`, with `open MeasureTheory Set Filter`, `open scoped Topology ENNReal`):
--
--   ```lean
--   theorem approximatingSolution_renormalized_average_compactness_q80
--       (f : Density) (hfm : Measurable f) (hf : ∀ p, 0 ≤ f p) (hi : Integrable (entropyMoment f))
--       (T R : ℕ → ℝ) (hT : ∀ j, 0 ≤ T j) (hR : ∀ j, 0 < R j)
--       (β : ℕ → Renormalization) (χ : ℕ → Published.KineticPhase → ℝ)
--       (hχ : ∀ j, ContDiff ℝ (⊤ : ℕ∞) (χ j)) (hχc : ∀ j, HasCompactSupport (χ j))
--       (hχx : ∀ j, tsupport (χ j) ⊆ {z | z.1.2 ∈ TorusChart.cube})
--       (hχv : ∀ j, tsupport (χ j) ⊆ {z | ‖z.2‖ ≤ R j})
--       (hχzero : ∀ j p, χ j (TransportCutoff.characteristic p 0) = 0)
--       (ψ : ℕ → Velocity → ℝ) (hψ : ∀ j, ContDiff ℝ (⊤ : ℕ∞) (ψ j))
--       (hψc : ∀ j, HasCompactSupport (ψ j)) :
--       ∃ (φ : ℕ → ℕ) (g : ℕ → Published.SpaceTime → ℝ), StrictMono φ ∧
--         ∀ j, LocallyIntegrable (g j) volume ∧ ∀ K : Set Published.SpaceTime, IsCompact K →
--           K ⊆ {z | z.1 ∈ Icc 0 (T j)} →
--           Tendsto (fun n => eLpNorm (fun z =>
--             (∫ v, ψ j v*(χ j (z,v)*
--               (approximatingSolution f hfm (φ n)).euclideanRenormalizedDensity (β j) (z,v)))-g j z)
--             1 (volume.restrict K)) atTop (𝓝 0)
--   ```
--
--   **Definitions.** The statement is written with `OAI.BoltzmannNonuniqueness.PeriodicApproximation.initialApproximation`, `OAI.BoltzmannNonuniqueness.Published.KineticPhase`, `OAI.BoltzmannNonuniqueness.Published.SpaceTime`, `OAI.BoltzmannNonuniqueness.Published.Velocity`, `OAI.BoltzmannNonuniqueness.TransportCutoff.characteristic` and `OAI.BoltzmannNonuniqueness.PeriodicApproximation.BoundedCutoffSolution.euclideanRenormalizedDensity` (definitions bundle `OAIQ080A000` of this split); `OAI.BoltzmannNonuniqueness.PeriodicApproximation.approximatingSolution` and `OAI.BoltzmannNonuniqueness.TorusChart.cube` (definitions bundle `OAIQ080A002` of this split); `OAI.BoltzmannNonuniqueness.Density`, `OAI.BoltzmannNonuniqueness.Phase`, `OAI.BoltzmannNonuniqueness.Position`, `OAI.BoltzmannNonuniqueness.Renormalization`, `OAI.BoltzmannNonuniqueness.Velocity` and `OAI.BoltzmannNonuniqueness.entropyMoment` (the published bundle `Def_BoltzmannNonuniqueness`).
--
--   **Used by.** The proof of `OAI.BoltzmannNonuniqueness.PeriodicApproximation.exists_global_density_pair_with_strong_mass_q80` of this split imports it.
-- source:
--   OpenAI, Nonuniqueness for the periodic hard-sphere Boltzmann equation (result family 363), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 363; paper: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/Nonuniqueness-for-the-periodic-hard-sphere-Boltzmann-equation-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/MathematicalPhysics/Boltzmann/Compactness/PeriodicWeakCompactness.lean (declaration OAI.BoltzmannNonuniqueness.PeriodicApproximation.approximatingSolution_renormalized_average_compactness)

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
open scoped Topology ENNReal
namespace BoltzmannNonuniqueness.PeriodicApproximation

theorem approximatingSolution_renormalized_average_compactness_q80
    (f : Density) (hfm : Measurable f) (hf : ∀ p, 0 ≤ f p) (hi : Integrable (entropyMoment f))
    (T R : ℕ → ℝ) (hT : ∀ j, 0 ≤ T j) (hR : ∀ j, 0 < R j)
    (β : ℕ → Renormalization) (χ : ℕ → Published.KineticPhase → ℝ)
    (hχ : ∀ j, ContDiff ℝ (⊤ : ℕ∞) (χ j)) (hχc : ∀ j, HasCompactSupport (χ j))
    (hχx : ∀ j, tsupport (χ j) ⊆ {z | z.1.2 ∈ TorusChart.cube})
    (hχv : ∀ j, tsupport (χ j) ⊆ {z | ‖z.2‖ ≤ R j})
    (hχzero : ∀ j p, χ j (TransportCutoff.characteristic p 0) = 0)
    (ψ : ℕ → Velocity → ℝ) (hψ : ∀ j, ContDiff ℝ (⊤ : ℕ∞) (ψ j))
    (hψc : ∀ j, HasCompactSupport (ψ j)) :
    ∃ (φ : ℕ → ℕ) (g : ℕ → Published.SpaceTime → ℝ), StrictMono φ ∧
      ∀ j, LocallyIntegrable (g j) volume ∧ ∀ K : Set Published.SpaceTime, IsCompact K →
        K ⊆ {z | z.1 ∈ Icc 0 (T j)} →
        Tendsto (fun n => eLpNorm (fun z =>
          (∫ v, ψ j v*(χ j (z,v)*
            (approximatingSolution f hfm (φ n)).euclideanRenormalizedDensity (β j) (z,v)))-g j z)
          1 (volume.restrict K)) atTop (𝓝 0) := by
  sorry

end BoltzmannNonuniqueness.PeriodicApproximation

end

end

end OAI
end
