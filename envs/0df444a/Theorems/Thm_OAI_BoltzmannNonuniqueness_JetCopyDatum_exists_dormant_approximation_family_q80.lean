-- Prove2me | Theorems.Thm_OAI_BoltzmannNonuniqueness_JetCopyDatum_exists_dormant_approximation_family_q80
-- name    : OAI.BoltzmannNonuniqueness.JetCopyDatum.exists_dormant_approximation_family_q80
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-31T19:26:37.9824+00:00
-- url     : https://prove2.me/theorems/11634057-2b56-421a-984e-84f33fa167f3
-- title:
--   OAI.BoltzmannNonuniqueness.JetCopyDatum.exists_dormant_approximation_family_q80: intermediate lemma from OpenAI, Nonuniqueness for the periodic hard-sphere Boltzmann equation (result family 363)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.BoltzmannNonuniqueness.nonuniqueness`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Nonuniqueness for the periodic hard-sphere Boltzmann equation (result family 363)*, OpenAI Math Release, September 23, 2026, result family 363, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.BoltzmannNonuniqueness.JetCopyDatum.exists_dormant_approximation_family` of [lean/OAI/MathematicalPhysics/Boltzmann/Approximation/DormantConstruction.lean](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/MathematicalPhysics/Boltzmann/Approximation/DormantConstruction.lean) at commit 1581d4c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.BoltzmannNonuniqueness.JetCopyDatum`, with `open MeasureTheory Set`, `open BoltzmannNonuniqueness.WeightedLocal BoltzmannNonuniqueness.WeightedLocalControl`, `open BoltzmannNonuniqueness.WeightedLocalControl.PeriodicMildState`):
--
--   ```lean
--   theorem exists_dormant_approximation_family_q80 (hcarleman : Published.GPV2009CarlemanInput)
--       {s₀ η K α γ d₀ q : ℝ}
--       (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8) (hη : 0 < η) (hηmax : η ≤ Real.log 2)
--       (hK : 0 ≤ K) (hα : 0 < α) (hαmax : α ≤ 1/4) (hγ : 0 < γ)
--       (hd₀ : 0 < d₀) (hd₀max : d₀ ≤ 1) (hwidth : d₀*(1/8:ℝ)^10 ≤ 1/64)
--       (hsmall : JetComparisonCoefficient.coefficient K*d₀*s₀^9 ≤ 1)
--       (hq₁ : 1 < q) (hq₂ : q < 2) :
--       ∃ T : ℝ, 0 < T ∧ T ≤ 1/32 ∧
--         ∃ F : ∀ N, BelowCap.Approximation s₀ η K α γ d₀ q T N,
--           (∀ N, (F N).coefficient = 0) ∧
--           ∀ N t, t ∈ Icc 0 T → PhaseEssSup.size (fun p => (F N).solution.value (t,p)-
--             ∑' i, rebuilt s₀ η K α γ d₀ q (N+1) (damping q (N+1) (F N).amplitude)
--               T N (F N).solution.value i (t,p)) ≤ t^2
--   ```
--
--   **Definitions.** The statement is written with `OAI.BoltzmannNonuniqueness.DatumBounds.scale`, `OAI.BoltzmannNonuniqueness.HotSeedProfile.normalized`, `OAI.BoltzmannNonuniqueness.JetComparisonCoefficient.coefficient`, `OAI.BoltzmannNonuniqueness.JetCopyDatum.initial`, `OAI.BoltzmannNonuniqueness.JetCopyDatum.rebuilt`, `OAI.BoltzmannNonuniqueness.JetLattice.Label`, `OAI.BoltzmannNonuniqueness.JetPrototype.Phase`, `OAI.BoltzmannNonuniqueness.PhaseEssSup.size`, `OAI.BoltzmannNonuniqueness.WeightedLocalControl.damping`, `OAI.BoltzmannNonuniqueness.JetCopyDatum.BelowCap.Approximation` and `OAI.BoltzmannNonuniqueness.WeightedLocalControl.PeriodicMildState` (definitions bundle `OAIQ080A000` of this split); `OAI.BoltzmannNonuniqueness.Published.GPV2009CarlemanInput` (definitions bundle `OAIQ080A002` of this split).
--
--   **Used by.** The proof of `OAI.BoltzmannNonuniqueness.JetCopyDatum.exists_dormant_family_q80` of this split imports it.
-- source:
--   OpenAI, Nonuniqueness for the periodic hard-sphere Boltzmann equation (result family 363), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 363; paper: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/Nonuniqueness-for-the-periodic-hard-sphere-Boltzmann-equation-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/MathematicalPhysics/Boltzmann/Approximation/DormantConstruction.lean (declaration OAI.BoltzmannNonuniqueness.JetCopyDatum.exists_dormant_approximation_family)

import Mathlib
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
open MeasureTheory Set
open BoltzmannNonuniqueness.WeightedLocal BoltzmannNonuniqueness.WeightedLocalControl
open BoltzmannNonuniqueness.WeightedLocalControl.PeriodicMildState
namespace BoltzmannNonuniqueness.JetCopyDatum

theorem exists_dormant_approximation_family_q80 (hcarleman : Published.GPV2009CarlemanInput)
    {s₀ η K α γ d₀ q : ℝ}
    (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8) (hη : 0 < η) (hηmax : η ≤ Real.log 2)
    (hK : 0 ≤ K) (hα : 0 < α) (hαmax : α ≤ 1/4) (hγ : 0 < γ)
    (hd₀ : 0 < d₀) (hd₀max : d₀ ≤ 1) (hwidth : d₀*(1/8:ℝ)^10 ≤ 1/64)
    (hsmall : JetComparisonCoefficient.coefficient K*d₀*s₀^9 ≤ 1)
    (hq₁ : 1 < q) (hq₂ : q < 2) :
    ∃ T : ℝ, 0 < T ∧ T ≤ 1/32 ∧
      ∃ F : ∀ N, BelowCap.Approximation s₀ η K α γ d₀ q T N,
        (∀ N, (F N).coefficient = 0) ∧
        ∀ N t, t ∈ Icc 0 T → PhaseEssSup.size (fun p => (F N).solution.value (t,p)-
          ∑' i, rebuilt s₀ η K α γ d₀ q (N+1) (damping q (N+1) (F N).amplitude)
            T N (F N).solution.value i (t,p)) ≤ t^2 := by
  sorry

end BoltzmannNonuniqueness.JetCopyDatum

end

end

end OAI
end
