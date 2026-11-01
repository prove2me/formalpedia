-- Prove2me | Theorems.Thm_OAI_BoltzmannNonuniqueness_JetCopyDatum_CapApproximation_escapedTotal_bound_global_q80
-- name    : OAI.BoltzmannNonuniqueness.JetCopyDatum.CapApproximation.escapedTotal_bound_global_q80
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-31T19:11:54.418346+00:00
-- url     : https://prove2.me/theorems/54999890-6eb3-47a1-a554-3c3f32c20a5f
-- title:
--   OAI.BoltzmannNonuniqueness.JetCopyDatum.CapApproximation.escapedTotal_bound_global_q80 (OpenAI intermediate lemma)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.BoltzmannNonuniqueness.nonuniqueness`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Nonuniqueness for the periodic hard-sphere Boltzmann equation (result family 363)*, OpenAI Math Release, September 23, 2026, result family 363, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.BoltzmannNonuniqueness.JetCopyDatum.CapApproximation.escapedTotal_bound_global` of [lean/OAI/MathematicalPhysics/Boltzmann/Approximation/CapColdBounds.lean](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/MathematicalPhysics/Boltzmann/Approximation/CapColdBounds.lean) at commit 1581d4c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.BoltzmannNonuniqueness.JetCopyDatum`, with `open MeasureTheory Set`, `open scoped ENNReal`, `open BoltzmannNonuniqueness.JetLattice BoltzmannNonuniqueness.JetGeometry`, `open BoltzmannNonuniqueness.JetPrototype BoltzmannNonuniqueness.VelocityWeight`):
--
--   ```lean
--   theorem CapApproximation.escapedTotal_bound_global_q80 {s₀ η K α γ d₀ q T : ℝ} {N : ℕ}
--       (F : CapApproximation s₀ η K α γ d₀ q T N)
--       (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8) (hη : 0 < η) (hηmax : η ≤ Real.log 2)
--       (hK : 0 ≤ K) (hα : 0 ≤ α) (hαmax : α ≤ 1) (hγ : 0 ≤ γ)
--       (hd₀ : 0 < d₀) (hd₀max : d₀ ≤ 1)
--       (hsmall : JetComparisonCoefficient.coefficient K*d₀*s₀^9 ≤ 1)
--       (hq : q < 2) (hT : 0 ≤ T) (hTmax : T ≤ 1/32)
--       (A : ℝ) {z : Published.KineticPhase} (ht : z.1.1 ∈ Ioc 0 T) :
--       F.escapedTotal z ≤ JetEscapedEnvelope.constant s₀ η α K d₀
--         (JetEscapedEnvelope.exponent A)*z.1.1^A
--   ```
--
--   **Definitions.** The statement is written with `OAI.BoltzmannNonuniqueness.JetComparisonCoefficient.coefficient`, `OAI.BoltzmannNonuniqueness.JetCopyDatum.CapApproximation`, `OAI.BoltzmannNonuniqueness.JetEscapedEnvelope.constant`, `OAI.BoltzmannNonuniqueness.JetEscapedEnvelope.exponent`, `OAI.BoltzmannNonuniqueness.Published.KineticPhase`, `OAI.BoltzmannNonuniqueness.Published.SpaceTime`, `OAI.BoltzmannNonuniqueness.Published.Velocity` and `OAI.BoltzmannNonuniqueness.JetCopyDatum.CapApproximation.escapedTotal` (definitions bundle `OAIQ080A000` of this split).
--
--   **Used by.** The proof of `OAI.BoltzmannNonuniqueness.JetCopyDatum.CapApproximation.normalized_mixed_gain_le_positive_q80` of this split imports it.
-- source:
--   OpenAI, Nonuniqueness for the periodic hard-sphere Boltzmann equation (result family 363), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 363; paper: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/Nonuniqueness-for-the-periodic-hard-sphere-Boltzmann-equation-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/MathematicalPhysics/Boltzmann/Approximation/CapColdBounds.lean (declaration OAI.BoltzmannNonuniqueness.JetCopyDatum.CapApproximation.escapedTotal_bound_global)

import Mathlib
import Definitions.Def_OAIQ080A000

section

attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.ChartKernel.offAxis_sFinite _root_.OAI.BoltzmannNonuniqueness.EuclideanFlight.sourcePullback_finite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.characteristicGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.retainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.coldCylinderVolume_finite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.copyColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.mainCoreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.selectedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.dilatedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.kineticColdKernel_sFinite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section

open MeasureTheory Set
open scoped ENNReal
open BoltzmannNonuniqueness.JetLattice BoltzmannNonuniqueness.JetGeometry
open BoltzmannNonuniqueness.JetPrototype BoltzmannNonuniqueness.VelocityWeight

namespace BoltzmannNonuniqueness.JetCopyDatum

theorem CapApproximation.escapedTotal_bound_global_q80 {s₀ η K α γ d₀ q T : ℝ} {N : ℕ}
    (F : CapApproximation s₀ η K α γ d₀ q T N)
    (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8) (hη : 0 < η) (hηmax : η ≤ Real.log 2)
    (hK : 0 ≤ K) (hα : 0 ≤ α) (hαmax : α ≤ 1) (hγ : 0 ≤ γ)
    (hd₀ : 0 < d₀) (hd₀max : d₀ ≤ 1)
    (hsmall : JetComparisonCoefficient.coefficient K*d₀*s₀^9 ≤ 1)
    (hq : q < 2) (hT : 0 ≤ T) (hTmax : T ≤ 1/32)
    (A : ℝ) {z : Published.KineticPhase} (ht : z.1.1 ∈ Ioc 0 T) :
    F.escapedTotal z ≤ JetEscapedEnvelope.constant s₀ η α K d₀
      (JetEscapedEnvelope.exponent A)*z.1.1^A := by
  sorry

end BoltzmannNonuniqueness.JetCopyDatum

end

end

end OAI
end
