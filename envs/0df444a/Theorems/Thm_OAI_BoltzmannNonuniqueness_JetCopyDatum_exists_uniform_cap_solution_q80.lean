-- Prove2me | Theorems.Thm_OAI_BoltzmannNonuniqueness_JetCopyDatum_exists_uniform_cap_solution_q80
-- name    : OAI.BoltzmannNonuniqueness.JetCopyDatum.exists_uniform_cap_solution_q80
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-31T19:27:00.482+00:00
-- url     : https://prove2.me/theorems/a9bcc63a-370c-4ba0-b492-cca53ae94b5c
-- title:
--   OAI.BoltzmannNonuniqueness.JetCopyDatum.exists_uniform_cap_solution_q80: intermediate lemma from OpenAI, Nonuniqueness for the periodic hard-sphere Boltzmann equation (result family 363)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.BoltzmannNonuniqueness.nonuniqueness`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Nonuniqueness for the periodic hard-sphere Boltzmann equation (result family 363)*, OpenAI Math Release, September 23, 2026, result family 363, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.BoltzmannNonuniqueness.JetCopyDatum.exists_uniform_cap_solution` of [lean/OAI/MathematicalPhysics/Boltzmann/Jets/JetFiniteCap.lean](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/MathematicalPhysics/Boltzmann/Jets/JetFiniteCap.lean) at commit 1581d4c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.BoltzmannNonuniqueness.JetCopyDatum`, with `open MeasureTheory Set`, `open BoltzmannNonuniqueness.WeightedLocal BoltzmannNonuniqueness.WeightedLocalControl`, `open BoltzmannNonuniqueness.WeightedLocalControl.PeriodicMildState`, `open BoltzmannNonuniqueness.WeightedTranslation`):
--
--   ```lean
--   theorem exists_uniform_cap_solution_q80 (hcarleman : Published.GPV2009CarlemanInput)
--       {s₀ η K α γ d₀ q : ℝ}
--       (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8) (hη : 0 < η) (hηmax : η ≤ Real.log 2)
--       (hK : 0 ≤ K) (hα : 0 < α) (hαmax : α ≤ 1/4) (hγ : 0 < γ)
--       (hd₀ : 0 < d₀) (hd₀max : d₀ ≤ 1) (hwidth : d₀*(1/8:ℝ)^10 ≤ 1/64)
--       (hsmall : JetComparisonCoefficient.coefficient K*d₀*s₀^9 ≤ 1)
--       (hq₁ : 1 < q) (hq₂ : q < 2) :
--       ∃ τ : ℝ, 0 < τ ∧ τ ≤ 1/32 ∧ ∀ (N : ℕ) (b T : ℝ), 0 ≤ b → 0 ≤ T → T ≤ τ →
--         ∃ (A ell : ℝ), 0 < A ∧ ell ∈ Icc 0 2 ∧
--           (∀ p, initial s₀ η K α γ d₀ q N
--             (fun p => ell*HotSeedProfile.normalized q (DatumBounds.scale s₀ η (N+1)) p) p ≤ 2*A) ∧
--           ∃ F : PeriodicMildState q b (damping q b A) T (2*A)
--             (initial s₀ η K α γ d₀ q N
--               (fun p => ell*HotSeedProfile.normalized q (DatumBounds.scale s₀ η (N+1)) p)),
--             F.hotPeak (DatumBounds.scale s₀ η (N+1)) (color s₀ η K α γ d₀ q N) = 1
--   ```
--
--   **Definitions.** The statement is written with `OAI.BoltzmannNonuniqueness.DatumBounds.scale`, `OAI.BoltzmannNonuniqueness.HotSeedProfile.normalized`, `OAI.BoltzmannNonuniqueness.JetComparisonCoefficient.coefficient`, `OAI.BoltzmannNonuniqueness.JetCopyDatum.color`, `OAI.BoltzmannNonuniqueness.JetCopyDatum.initial`, `OAI.BoltzmannNonuniqueness.JetCopyDatum.instCountableLabel`, `OAI.BoltzmannNonuniqueness.JetLattice.Label`, `OAI.BoltzmannNonuniqueness.JetPrototype.Phase`, `OAI.BoltzmannNonuniqueness.WeightedLocalControl.PeriodicMildState`, `OAI.BoltzmannNonuniqueness.WeightedLocalControl.damping` and `OAI.BoltzmannNonuniqueness.WeightedLocalControl.PeriodicMildState.hotPeak` (definitions bundle `OAIQ080A000` of this split); `OAI.BoltzmannNonuniqueness.Published.GPV2009CarlemanInput` (definitions bundle `OAIQ080A002` of this split).
--
--   **Used by.** The proof of `OAI.BoltzmannNonuniqueness.JetCopyDatum.exists_tight_cap_family_at_q80` of this split imports it.
-- source:
--   OpenAI, Nonuniqueness for the periodic hard-sphere Boltzmann equation (result family 363), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 363; paper: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/Nonuniqueness-for-the-periodic-hard-sphere-Boltzmann-equation-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/MathematicalPhysics/Boltzmann/Jets/JetFiniteCap.lean (declaration OAI.BoltzmannNonuniqueness.JetCopyDatum.exists_uniform_cap_solution)

import Mathlib
import Definitions.Def_OAIQ080A002

section

attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.ChartKernel.offAxis_sFinite _root_.OAI.BoltzmannNonuniqueness.EuclideanFlight.sourcePullback_finite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.characteristicGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.hotKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.mixedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.retainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.coldCylinderVolume_finite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.copyColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.mainCoreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.selectedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.dilatedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.kineticColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.awayOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.nearOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalRetainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.densityScaledCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalBeamKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalPhysicalEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalWindowEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalEventMeasure_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.scaledBeamNormalKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseEndpointKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseIncrement_finite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseSeed_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.residenceKernel_sFinite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section

open MeasureTheory Set
open BoltzmannNonuniqueness.WeightedLocal BoltzmannNonuniqueness.WeightedLocalControl
open BoltzmannNonuniqueness.WeightedLocalControl.PeriodicMildState
open BoltzmannNonuniqueness.WeightedTranslation

namespace BoltzmannNonuniqueness.JetCopyDatum

theorem exists_uniform_cap_solution_q80 (hcarleman : Published.GPV2009CarlemanInput)
    {s₀ η K α γ d₀ q : ℝ}
    (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8) (hη : 0 < η) (hηmax : η ≤ Real.log 2)
    (hK : 0 ≤ K) (hα : 0 < α) (hαmax : α ≤ 1/4) (hγ : 0 < γ)
    (hd₀ : 0 < d₀) (hd₀max : d₀ ≤ 1) (hwidth : d₀*(1/8:ℝ)^10 ≤ 1/64)
    (hsmall : JetComparisonCoefficient.coefficient K*d₀*s₀^9 ≤ 1)
    (hq₁ : 1 < q) (hq₂ : q < 2) :
    ∃ τ : ℝ, 0 < τ ∧ τ ≤ 1/32 ∧ ∀ (N : ℕ) (b T : ℝ), 0 ≤ b → 0 ≤ T → T ≤ τ →
      ∃ (A ell : ℝ), 0 < A ∧ ell ∈ Icc 0 2 ∧
        (∀ p, initial s₀ η K α γ d₀ q N
          (fun p => ell*HotSeedProfile.normalized q (DatumBounds.scale s₀ η (N+1)) p) p ≤ 2*A) ∧
        ∃ F : PeriodicMildState q b (damping q b A) T (2*A)
          (initial s₀ η K α γ d₀ q N
            (fun p => ell*HotSeedProfile.normalized q (DatumBounds.scale s₀ η (N+1)) p)),
          F.hotPeak (DatumBounds.scale s₀ η (N+1)) (color s₀ η K α γ d₀ q N) = 1 := by
  sorry

end BoltzmannNonuniqueness.JetCopyDatum

end

end

end OAI
end
