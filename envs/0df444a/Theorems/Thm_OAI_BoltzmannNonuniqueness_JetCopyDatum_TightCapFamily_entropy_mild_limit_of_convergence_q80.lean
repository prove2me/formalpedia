-- Prove2me | Theorems.Thm_OAI_BoltzmannNonuniqueness_JetCopyDatum_TightCapFamily_entropy_mild_limit_of_convergence_q80
-- name    : OAI.BoltzmannNonuniqueness.JetCopyDatum.TightCapFamily.entropy_mild_limit_of_convergence_q80
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-31T19:25:10.599093+00:00
-- url     : https://prove2.me/theorems/56a7618c-b3cf-4893-bdff-bdbc4d08dba1
-- title:
--   OAI.BoltzmannNonuniqueness.JetCopyDatum.TightCapFamily.entropy_mild_limit_of_convergence_q80 (OpenAI intermediate lemma)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.BoltzmannNonuniqueness.nonuniqueness`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Nonuniqueness for the periodic hard-sphere Boltzmann equation (result family 363)*, OpenAI Math Release, September 23, 2026, result family 363, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.BoltzmannNonuniqueness.JetCopyDatum.TightCapFamily.entropy_mild_limit_of_convergence` of [lean/OAI/MathematicalPhysics/Boltzmann/Approximation/CapEntropyMoments.lean](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/MathematicalPhysics/Boltzmann/Approximation/CapEntropyMoments.lean) at commit 1581d4c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.BoltzmannNonuniqueness.JetCopyDatum`, with `open MeasureTheory Set Filter`, `open scoped ENNReal Topology`):
--
--   ```lean
--   theorem TightCapFamily.entropy_mild_limit_of_convergence_q80
--       (hcarleman : Published.GPV2009CarlemanInput)
--       {s₀ η K α γ d₀ q : ℝ} (F : TightCapFamily s₀ η K α γ d₀ q)
--       (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8) (hη : 0 < η) (hηmax : η ≤ Real.log 2)
--       (hK : 0 < K) (hγ : 0 < γ) (hd₀ : 0 < d₀)
--       (hwidth : d₀*(1/8:ℝ)^10 ≤ 1/64) (hα : 0 ≤ α) (hαmax : α ≤ 1/4)
--       (hq₁ : 1 < q) (hq₂ : q < 2)
--       {φ : ℕ → ℕ} {g : (ℝ × Position) × Velocity → ℝ} (hφ : StrictMono φ)
--       (S : MildCollisionSolution F.time (JetPeriodicDatum.datum s₀ η K α γ d₀) g)
--       (hpair : Published.WeakL1Converges ((AnnularEnvelope.timePositionVolume F.time).prod volume)
--         (fun n => CollisionCompactness.pairDensity
--           (torusPhysical q (F.approximation (φ n)).solution.value)) (CollisionCompactness.pairDensity g))
--       (htrace : ∀ t ∈ Icc 0 F.time, Published.WeakL1Converges volume
--         (fun n p => torusPhysical q (F.approximation (φ n)).solution.value ((t,p.1),p.2))
--         (MildCollisionSolution.positiveEvolution F.time (JetPeriodicDatum.datum s₀ η K α γ d₀) g t)) :
--       ∀ t ∈ Ioc 0 F.time,
--           (∫⁻ z, ENNReal.ofReal (scalarRelativeEntropy (maxwellian z.2)
--             (MildCollisionSolution.positiveEvolution F.time (JetPeriodicDatum.datum s₀ η K α γ d₀) g t z)))+
--           CollisionCompactness.rateDissipation (AnnularEnvelope.timePositionVolume t) g ≤
--             ENNReal.ofReal (relativeEntropy (JetPeriodicDatum.datum s₀ η K α γ d₀))
--   ```
--
--   **Definitions.** The statement is written with `OAI.BoltzmannNonuniqueness.MildCollisionSolution`, `OAI.BoltzmannNonuniqueness.AnnularEnvelope.timePositionVolume`, `OAI.BoltzmannNonuniqueness.CollisionCompactness.pairDensity`, `OAI.BoltzmannNonuniqueness.CollisionCompactness.rateDissipation`, `OAI.BoltzmannNonuniqueness.DatumBounds.scale`, `OAI.BoltzmannNonuniqueness.HotSeedProfile.normalized`, `OAI.BoltzmannNonuniqueness.JetCopyDatum.TightCapFamily`, `OAI.BoltzmannNonuniqueness.JetCopyDatum.initial`, `OAI.BoltzmannNonuniqueness.JetCopyDatum.torusPhysical`, `OAI.BoltzmannNonuniqueness.JetPeriodicDatum.datum`, `OAI.BoltzmannNonuniqueness.JetPrototype.Phase`, `OAI.BoltzmannNonuniqueness.MildCollisionSolution.positiveEvolution`, `OAI.BoltzmannNonuniqueness.Published.WeakL1Converges`, `OAI.BoltzmannNonuniqueness.WeightedLocalControl.damping`, `OAI.BoltzmannNonuniqueness.JetCopyDatum.CapApproximation`, `OAI.BoltzmannNonuniqueness.JetCopyDatum.CompactCapFamily` and `OAI.BoltzmannNonuniqueness.WeightedLocalControl.PeriodicMildState` (definitions bundle `OAIQ080A000` of this split); `OAI.BoltzmannNonuniqueness.scalarRelativeEntropy` (definitions bundle `OAIQ080A001` of this split); `OAI.BoltzmannNonuniqueness.Published.GPV2009CarlemanInput` (definitions bundle `OAIQ080A002` of this split); `OAI.BoltzmannNonuniqueness.Phase`, `OAI.BoltzmannNonuniqueness.Position`, `OAI.BoltzmannNonuniqueness.Velocity`, `OAI.BoltzmannNonuniqueness.maxwellian` and `OAI.BoltzmannNonuniqueness.relativeEntropy` (the published bundle `Def_BoltzmannNonuniqueness`).
--
--   **Used by.** The proof of `OAI.BoltzmannNonuniqueness.JetCopyDatum.TightCapFamily.exists_limit_q80` of this split imports it.
-- source:
--   OpenAI, Nonuniqueness for the periodic hard-sphere Boltzmann equation (result family 363), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 363; paper: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/Nonuniqueness-for-the-periodic-hard-sphere-Boltzmann-equation-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/MathematicalPhysics/Boltzmann/Approximation/CapEntropyMoments.lean (declaration OAI.BoltzmannNonuniqueness.JetCopyDatum.TightCapFamily.entropy_mild_limit_of_convergence)

import Mathlib
import Definitions.Def_BoltzmannNonuniqueness
import Definitions.Def_OAIQ080A002

section

attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.ChartKernel.offAxis_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.characteristicGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.retainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.copyColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.mainCoreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.selectedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.dilatedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.kineticColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.awayOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.nearOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalRetainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.densityScaledCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalBeamKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalPhysicalEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalWindowEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalEventMeasure_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.scaledBeamNormalKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseEndpointKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseSeed_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.residenceKernel_sFinite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal Topology

namespace BoltzmannNonuniqueness.JetCopyDatum

theorem TightCapFamily.entropy_mild_limit_of_convergence_q80
    (hcarleman : Published.GPV2009CarlemanInput)
    {s₀ η K α γ d₀ q : ℝ} (F : TightCapFamily s₀ η K α γ d₀ q)
    (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8) (hη : 0 < η) (hηmax : η ≤ Real.log 2)
    (hK : 0 < K) (hγ : 0 < γ) (hd₀ : 0 < d₀)
    (hwidth : d₀*(1/8:ℝ)^10 ≤ 1/64) (hα : 0 ≤ α) (hαmax : α ≤ 1/4)
    (hq₁ : 1 < q) (hq₂ : q < 2)
    {φ : ℕ → ℕ} {g : (ℝ × Position) × Velocity → ℝ} (hφ : StrictMono φ)
    (S : MildCollisionSolution F.time (JetPeriodicDatum.datum s₀ η K α γ d₀) g)
    (hpair : Published.WeakL1Converges ((AnnularEnvelope.timePositionVolume F.time).prod volume)
      (fun n => CollisionCompactness.pairDensity
        (torusPhysical q (F.approximation (φ n)).solution.value)) (CollisionCompactness.pairDensity g))
    (htrace : ∀ t ∈ Icc 0 F.time, Published.WeakL1Converges volume
      (fun n p => torusPhysical q (F.approximation (φ n)).solution.value ((t,p.1),p.2))
      (MildCollisionSolution.positiveEvolution F.time (JetPeriodicDatum.datum s₀ η K α γ d₀) g t)) :
    ∀ t ∈ Ioc 0 F.time,
        (∫⁻ z, ENNReal.ofReal (scalarRelativeEntropy (maxwellian z.2)
          (MildCollisionSolution.positiveEvolution F.time (JetPeriodicDatum.datum s₀ η K α γ d₀) g t z)))+
        CollisionCompactness.rateDissipation (AnnularEnvelope.timePositionVolume t) g ≤
          ENNReal.ofReal (relativeEntropy (JetPeriodicDatum.datum s₀ η K α γ d₀)) := by
  sorry

end BoltzmannNonuniqueness.JetCopyDatum

end

end

end OAI
end
