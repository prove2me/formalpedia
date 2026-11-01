-- Prove2me | Theorems.Thm_OAI_BoltzmannNonuniqueness_JetCopyDatum_BelowCap_cap_family_cutoff_uniformIntegrable_q80
-- name    : OAI.BoltzmannNonuniqueness.JetCopyDatum.BelowCap.cap_family_cutoff_uniformIntegrable_q80
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-31T19:13:03.26699+00:00
-- url     : https://prove2.me/theorems/739cac71-d450-41a5-9a36-80f081a48d2c
-- title:
--   OAI.BoltzmannNonuniqueness.JetCopyDatum.BelowCap.cap_family_cutoff_uniformIntegrable_q80 (OpenAI intermediate lemma)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.BoltzmannNonuniqueness.nonuniqueness`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Nonuniqueness for the periodic hard-sphere Boltzmann equation (result family 363)*, OpenAI Math Release, September 23, 2026, result family 363, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.BoltzmannNonuniqueness.JetCopyDatum.BelowCap.cap_family_cutoff_uniformIntegrable` of [lean/OAI/MathematicalPhysics/Boltzmann/Approximation/SubcapMildLimits.lean](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/MathematicalPhysics/Boltzmann/Approximation/SubcapMildLimits.lean) at commit 1581d4c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.BoltzmannNonuniqueness.JetCopyDatum.BelowCap`, with `open MeasureTheory Set Filter`, `open scoped ENNReal Topology`, `open BoltzmannNonuniqueness.WeightedLocalControl`):
--
--   ```lean
--   theorem cap_family_cutoff_uniformIntegrable_q80 {s₀ η K α γ d₀ q T : ℝ}
--       (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8) (hη : 0 < η) (hηmax : η ≤ Real.log 2)
--       (hK : 0 ≤ K) (hα : 0 < α) (hαmax : α ≤ 1) (hγ : 0 < γ)
--       (hd₀ : 0 < d₀) (hd₀max : d₀ ≤ 1)
--       (hsmall : JetComparisonCoefficient.coefficient K*d₀*s₀^9 ≤ 1)
--       (hq : q < 2) (hT : 0 ≤ T) (hTmax : T ≤ 1/32)
--       (F : ∀ N, Approximation s₀ η K α γ d₀ q T N) :
--       UniformIntegrable (fun (N : ℕ) => KineticCollisionNullSets.gain (N+1) (torusPhysical q (F N).solution.value)) 1
--         ((AnnularEnvelope.timePositionVolume T).prod (volume : Measure Velocity)) ∧
--       UniformIntegrable (fun (N : ℕ) => CollisionCompactness.cutoffLossDensity (N+1) (torusPhysical q (F N).solution.value)) 1
--         ((AnnularEnvelope.timePositionVolume T).prod (volume : Measure Velocity))
--   ```
--
--   **Definitions.** The statement is written with `OAI.UniformIntegrable`, `OAI.BoltzmannNonuniqueness.AnnularEnvelope.timePositionVolume`, `OAI.BoltzmannNonuniqueness.CollisionCompactness.cutoffLossDensity`, `OAI.BoltzmannNonuniqueness.DatumBounds.scale`, `OAI.BoltzmannNonuniqueness.HotSeedProfile.normalized`, `OAI.BoltzmannNonuniqueness.JetComparisonCoefficient.coefficient`, `OAI.BoltzmannNonuniqueness.JetCopyDatum.initial`, `OAI.BoltzmannNonuniqueness.JetCopyDatum.torusPhysical`, `OAI.BoltzmannNonuniqueness.JetPrototype.Phase`, `OAI.BoltzmannNonuniqueness.KineticCollisionNullSets.gain`, `OAI.BoltzmannNonuniqueness.WeightedLocalControl.damping`, `OAI.BoltzmannNonuniqueness.JetCopyDatum.BelowCap.Approximation` and `OAI.BoltzmannNonuniqueness.WeightedLocalControl.PeriodicMildState` (definitions bundle `OAIQ080A000` of this split); `OAI.BoltzmannNonuniqueness.Position` and `OAI.BoltzmannNonuniqueness.Velocity` (the published bundle `Def_BoltzmannNonuniqueness`).
--
--   **Used by.** The proof of `OAI.BoltzmannNonuniqueness.JetCopyDatum.exists_dormant_family_q80` of this split imports it.
-- source:
--   OpenAI, Nonuniqueness for the periodic hard-sphere Boltzmann equation (result family 363), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 363; paper: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/Nonuniqueness-for-the-periodic-hard-sphere-Boltzmann-equation-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/MathematicalPhysics/Boltzmann/Approximation/SubcapMildLimits.lean (declaration OAI.BoltzmannNonuniqueness.JetCopyDatum.BelowCap.cap_family_cutoff_uniformIntegrable)

import Mathlib
import Definitions.Def_BoltzmannNonuniqueness
import Definitions.Def_OAIQ080A000

section

attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.ChartKernel.offAxis_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.characteristicGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.retainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.copyColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.mainCoreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.selectedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.dilatedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.kineticColdKernel_sFinite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal Topology
open BoltzmannNonuniqueness.WeightedLocalControl

namespace BoltzmannNonuniqueness.JetCopyDatum.BelowCap

theorem cap_family_cutoff_uniformIntegrable_q80 {s₀ η K α γ d₀ q T : ℝ}
    (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8) (hη : 0 < η) (hηmax : η ≤ Real.log 2)
    (hK : 0 ≤ K) (hα : 0 < α) (hαmax : α ≤ 1) (hγ : 0 < γ)
    (hd₀ : 0 < d₀) (hd₀max : d₀ ≤ 1)
    (hsmall : JetComparisonCoefficient.coefficient K*d₀*s₀^9 ≤ 1)
    (hq : q < 2) (hT : 0 ≤ T) (hTmax : T ≤ 1/32)
    (F : ∀ N, Approximation s₀ η K α γ d₀ q T N) :
    UniformIntegrable (fun (N : ℕ) => KineticCollisionNullSets.gain (N+1) (torusPhysical q (F N).solution.value)) 1
      ((AnnularEnvelope.timePositionVolume T).prod (volume : Measure Velocity)) ∧
    UniformIntegrable (fun (N : ℕ) => CollisionCompactness.cutoffLossDensity (N+1) (torusPhysical q (F N).solution.value)) 1
      ((AnnularEnvelope.timePositionVolume T).prod (volume : Measure Velocity)) := by
  sorry

end BoltzmannNonuniqueness.JetCopyDatum.BelowCap

end

end

end OAI
end
