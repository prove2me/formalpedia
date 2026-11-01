-- Prove2me | Theorems.Thm_OAI_BoltzmannNonuniqueness_PeriodicApproximation_approximatingSolution_renormalizedLocalizedSource_uniformIntegrable_q80
-- name    : OAI.BoltzmannNonuniqueness.PeriodicApproximation.approximatingSolution_renormalizedLocalizedSource_uniformIntegrable_q80
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-31T19:31:15.634988+00:00
-- url     : https://prove2.me/theorems/2aebc62b-a94d-49c4-a825-286f61448b9d
-- title:
--   OAI.BoltzmannNonuniqueness.PeriodicApproximation.approximatingSolution_renormalizedLocalizedSource_uniformIntegrable_q80 (OpenAI intermediate lemma)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.BoltzmannNonuniqueness.nonuniqueness`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Nonuniqueness for the periodic hard-sphere Boltzmann equation (result family 363)*, OpenAI Math Release, September 23, 2026, result family 363, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.BoltzmannNonuniqueness.PeriodicApproximation.approximatingSolution_renormalizedLocalizedSource_uniformIntegrable` of [lean/OAI/MathematicalPhysics/Boltzmann/Compactness/PeriodicWeakCompactness.lean](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/MathematicalPhysics/Boltzmann/Compactness/PeriodicWeakCompactness.lean) at commit 1581d4c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.BoltzmannNonuniqueness.PeriodicApproximation`, with `open MeasureTheory Set`):
--
--   ```lean
--   theorem approximatingSolution_renormalizedLocalizedSource_uniformIntegrable_q80
--       (f : Density) (hfm : Measurable f) (hf : ∀ p, 0 ≤ f p)
--       (hi : Integrable (entropyMoment f)) {T : ℝ} (hT : 0 ≤ T) (β : Renormalization)
--       {χ : Published.KineticPhase → ℝ} (hχ : ContDiff ℝ (⊤ : ℕ∞) χ)
--       (hc : HasCompactSupport χ) (hs : tsupport χ ⊆ {z | z.1.2 ∈ TorusChart.cube}) :
--       UniformIntegrable (fun n => TransportCutoff.localizedSource T χ
--         ((approximatingSolution f hfm (n+Nat.ceil T)).euclideanRenormalizedDensity β)
--         ((approximatingSolution f hfm (n+Nat.ceil T)).euclideanRenormalizedSource β)) 1 volume
--   ```
--
--   **Definitions.** The statement is written with `OAI.UniformIntegrable`, `OAI.BoltzmannNonuniqueness.PeriodicApproximation.initialApproximation`, `OAI.BoltzmannNonuniqueness.Published.KineticPhase`, `OAI.BoltzmannNonuniqueness.Published.SpaceTime`, `OAI.BoltzmannNonuniqueness.Published.Velocity`, `OAI.BoltzmannNonuniqueness.PeriodicApproximation.BoundedCutoffSolution.euclideanRenormalizedDensity` and `OAI.BoltzmannNonuniqueness.PeriodicApproximation.BoundedCutoffSolution.euclideanRenormalizedSource` (definitions bundle `OAIQ080A000` of this split); `OAI.BoltzmannNonuniqueness.PeriodicApproximation.approximatingSolution`, `OAI.BoltzmannNonuniqueness.TorusChart.cube` and `OAI.BoltzmannNonuniqueness.TransportCutoff.localizedSource` (definitions bundle `OAIQ080A002` of this split); `OAI.BoltzmannNonuniqueness.Density`, `OAI.BoltzmannNonuniqueness.Phase`, `OAI.BoltzmannNonuniqueness.Position`, `OAI.BoltzmannNonuniqueness.Renormalization`, `OAI.BoltzmannNonuniqueness.Velocity` and `OAI.BoltzmannNonuniqueness.entropyMoment` (the published bundle `Def_BoltzmannNonuniqueness`).
--
--   **Used by.** The proof of `OAI.BoltzmannNonuniqueness.PeriodicApproximation.approximatingSolution_renormalized_average_compactness_q80` of this split imports it.
-- source:
--   OpenAI, Nonuniqueness for the periodic hard-sphere Boltzmann equation (result family 363), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 363; paper: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/Nonuniqueness-for-the-periodic-hard-sphere-Boltzmann-equation-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/MathematicalPhysics/Boltzmann/Compactness/PeriodicWeakCompactness.lean (declaration OAI.BoltzmannNonuniqueness.PeriodicApproximation.approximatingSolution_renormalizedLocalizedSource_uniformIntegrable)

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
open MeasureTheory Set
namespace BoltzmannNonuniqueness.PeriodicApproximation
variable {N U : ℝ} {f₀ : Density}

theorem approximatingSolution_renormalizedLocalizedSource_uniformIntegrable_q80
    (f : Density) (hfm : Measurable f) (hf : ∀ p, 0 ≤ f p)
    (hi : Integrable (entropyMoment f)) {T : ℝ} (hT : 0 ≤ T) (β : Renormalization)
    {χ : Published.KineticPhase → ℝ} (hχ : ContDiff ℝ (⊤ : ℕ∞) χ)
    (hc : HasCompactSupport χ) (hs : tsupport χ ⊆ {z | z.1.2 ∈ TorusChart.cube}) :
    UniformIntegrable (fun n => TransportCutoff.localizedSource T χ
      ((approximatingSolution f hfm (n+Nat.ceil T)).euclideanRenormalizedDensity β)
      ((approximatingSolution f hfm (n+Nat.ceil T)).euclideanRenormalizedSource β)) 1 volume := by
  sorry

end BoltzmannNonuniqueness.PeriodicApproximation

end

end

end OAI
end
