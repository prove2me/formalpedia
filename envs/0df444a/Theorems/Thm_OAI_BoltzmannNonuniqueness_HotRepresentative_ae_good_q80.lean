-- Prove2me | Theorems.Thm_OAI_BoltzmannNonuniqueness_HotRepresentative_ae_good_q80
-- name    : OAI.BoltzmannNonuniqueness.HotRepresentative.ae_good_q80
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-31T19:17:24.776041+00:00
-- url     : https://prove2.me/theorems/fcb17167-98e4-4688-b837-3d6bb8266b89
-- title:
--   OAI.BoltzmannNonuniqueness.HotRepresentative.ae_good_q80: intermediate lemma from OpenAI, Nonuniqueness for the periodic hard-sphere Boltzmann equation (result family 363)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.BoltzmannNonuniqueness.nonuniqueness`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Nonuniqueness for the periodic hard-sphere Boltzmann equation (result family 363)*, OpenAI Math Release, September 23, 2026, result family 363, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.BoltzmannNonuniqueness.HotRepresentative.ae_good` of [lean/OAI/MathematicalPhysics/Boltzmann/Branching/HotPhysicalSource.lean](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/MathematicalPhysics/Boltzmann/Branching/HotPhysicalSource.lean) at commit 1581d4c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.BoltzmannNonuniqueness.HotRepresentative`, with `open MeasureTheory Set`, `open scoped ENNReal`, `open BoltzmannNonuniqueness.VelocityWeight BoltzmannNonuniqueness.ChartKernel`):
--
--   ```lean
--   theorem ae_good_q80 (hcarleman : Published.GPV2009CarlemanInput)
--       {q : ℝ} (hq₁ : 1 < q) (hq₂ : q < 2) : ∀ᵐ v : Velocity, v ∈ good q
--   ```
--
--   **Definitions.** The statement is written with `OAI.BoltzmannNonuniqueness.HotRepresentative.good` (definitions bundle `OAIQ080A000` of this split); `OAI.BoltzmannNonuniqueness.Published.GPV2009CarlemanInput` (definitions bundle `OAIQ080A002` of this split); `OAI.BoltzmannNonuniqueness.Velocity` (the published bundle `Def_BoltzmannNonuniqueness`).
--
--   **Used by.** The proofs of `OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.positive_coefficient_subsequence_q80`, `OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotPairExtraction.characteristic_test_balance_q80`, `OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.eventually_attained_boundedHotRatio_log_residual_q80`, `OAI.BoltzmannNonuniqueness.JetCopyDatum.BelowCap.TightFamily.entropy_mild_limit_of_convergence_q80`, `OAI.BoltzmannNonuniqueness.JetCopyDatum.BelowCap.TightFamily.exists_mild_limit_with_convergence_q80`, `OAI.BoltzmannNonuniqueness.JetCopyDatum.BelowCap.TightFamily.exists_mild_limit_with_traces_and_convergence_q80`, `OAI.BoltzmannNonuniqueness.JetCopyDatum.TightCapFamily.entropy_mild_limit_of_convergence_q80`, `OAI.BoltzmannNonuniqueness.JetCopyDatum.TightCapFamily.exists_mild_limit_with_convergence_q80`, `OAI.BoltzmannNonuniqueness.JetCopyDatum.TightCapFamily.exists_mild_limit_with_traces_and_convergence_q80` and `OAI.BoltzmannNonuniqueness.JetCopyDatum.uniform_hot_source_q80` of this split import it.
-- source:
--   OpenAI, Nonuniqueness for the periodic hard-sphere Boltzmann equation (result family 363), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 363; paper: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/Nonuniqueness-for-the-periodic-hard-sphere-Boltzmann-equation-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/MathematicalPhysics/Boltzmann/Branching/HotPhysicalSource.lean (declaration OAI.BoltzmannNonuniqueness.HotRepresentative.ae_good)

import Mathlib
import Definitions.Def_BoltzmannNonuniqueness
import Definitions.Def_OAIQ080A002

section

attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.ChartKernel.offAxis_sFinite _root_.OAI.BoltzmannNonuniqueness.EuclideanFlight.sourcePullback_finite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.characteristicGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.hotKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.mixedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.retainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.copyColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.mainCoreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.selectedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.dilatedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.kineticColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PeriodicApproximation.fiberMeasure_finite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.awayOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.nearOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalRetainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.densityScaledCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalBeamKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalPhysicalEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalWindowEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalEventMeasure_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.scaledBeamNormalKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseEndpointKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseIncrement_finite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseSeed_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.residenceKernel_sFinite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section

open MeasureTheory Set
open scoped ENNReal
open BoltzmannNonuniqueness.VelocityWeight BoltzmannNonuniqueness.ChartKernel

namespace BoltzmannNonuniqueness.HotRepresentative

theorem ae_good_q80 (hcarleman : Published.GPV2009CarlemanInput)
    {q : ℝ} (hq₁ : 1 < q) (hq₂ : q < 2) : ∀ᵐ v : Velocity, v ∈ good q := by
  sorry

end BoltzmannNonuniqueness.HotRepresentative

end

end

end OAI
end
