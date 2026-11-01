-- Prove2me | Theorems.Thm_OAI_BoltzmannNonuniqueness_JetCopyDatum_AttainedCapSequence_HotPairExtraction_positive_history_transfer_q80
-- name    : OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotPairExtraction.positive_history_transfer_q80
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-31T19:20:05.604658+00:00
-- url     : https://prove2.me/theorems/b8f1cfb3-9658-47d2-a68b-f3e5ade6c9e1
-- title:
--   OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotPairExtraction.positive_history_transfer_q80 (OpenAI intermediate lemma)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.BoltzmannNonuniqueness.nonuniqueness`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Nonuniqueness for the periodic hard-sphere Boltzmann equation (result family 363)*, OpenAI Math Release, September 23, 2026, result family 363, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotPairExtraction.positive_history_transfer` of [lean/OAI/MathematicalPhysics/Boltzmann/Approximation/CapAnnularMassGrowth.lean](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/MathematicalPhysics/Boltzmann/Approximation/CapAnnularMassGrowth.lean) at commit 1581d4c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence`, with `open MeasureTheory ProbabilityTheory Set`, `open scoped ENNReal ProbabilityTheory`, `open BoltzmannNonuniqueness.EuclideanFlight BoltzmannNonuniqueness.ReferenceGeometry`):
--
--   ```lean
--   theorem HotPairExtraction.positive_history_transfer_q80
--       (hDP : Published.DunfordPettis1940HotPairWindows)
--       (hcarleman : Published.GPV2009CarlemanInput) (hGLPS : Published.GLPS1988Proposition3)
--       (E : HotPairExtraction S)
--       (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8) (hη : 0 < η) (hηmax : η ≤ Real.log 2)
--       (hK : 0 ≤ K) (hα : 0 < α) (hαmax : α ≤ 1/4) (hγ : 0 < γ)
--       (hd₀ : 0 < d₀) (hd₀max : d₀ ≤ 1)
--       (hsmall : JetComparisonCoefficient.coefficient K*d₀*s₀^9 ≤ 1)
--       (hq₁ : 1 < q) (hq₂ : q < 2)
--       {a U V C r : ℝ} (ha : 0 < a) (haU : a < U) (hUV : U < V)
--       (hV : ENNReal.ofReal V < E.horizon) (hC : 0 ≤ C) (hr : 0 < r)
--       {β : WeakTime.Phase → ℝ} (hβ : ContDiff ℝ (⊤ : ℕ∞) β)
--       (hβc : HasCompactSupport β) (hβn : ∀ p, 0 ≤ β p) (hβ₁ : ∀ p, β p ≤ 1)
--       (hfrequency : ∀ u : CharacteristicPhase, u.1 ∈ Ioo a U → u.2 ∈ tsupport β →
--         E.toHotLimitExtraction.characteristicFrequency u ≤ C)
--       {Ω : Set CharacteristicPhase} (hΩ : MeasurableSet Ω) (hcore : ∀ z ∈ Ω, β z.2 = 1)
--       (A B : ℝ → Set WeakTime.Phase) (hA : ∀ t, MeasurableSet (A t))
--       (hB : ∀ s, MeasurableSet (B s))
--       (hstart : ∀ s ∈ Ioo a U, ∀ p ∈ B s, β p = 1)
--       (N : ℕ) (P : ℝ → ℝ → Prop)
--       (horder : ∀ s ∈ Ioo a U, ∀ t ∈ Ioo a U, P s t → s ≤ t)
--       (hpoint : ∀ s ∈ Ioo a U, ∀ t ∈ Ioo a U, P s t → ∀ p ∈ B s,
--         0 < (WeakTime.phaseEndpointKernel C t ∘ₖ
--           ((((localizedNormalBeamKernel
--             (GeometricBackground.beamCoefficients (zero_lt_one.trans_le E.phase_mem.1)
--               hα.le hγ.le η r) (K/(4*r)) C a η E.fraction hΩ).restrict
--             (measurable_fst measurableSet_Ioc : MeasurableSet (Prod.fst ⁻¹' Ioc s t))) ∘ₖ
--               WeakTime.residenceKernel C t)^N)) (s,p) (A t)) :
--       ∀ᵐ s ∂volume, ∀ᵐ t ∂volume, s ∈ Ioo a U → t ∈ Ioo a U → P s t →
--         0 < hotPhaseSlice E.hotLimit s (B s) → 0 < hotPhaseSlice E.hotLimit t (A t)
--   ```
--
--   **Definitions.** The statement is written with `OAI.BoltzmannNonuniqueness.EuclideanFlight.CharacteristicPhase`, `OAI.BoltzmannNonuniqueness.EuclideanFlight.hotPhaseSlice`, `OAI.BoltzmannNonuniqueness.GeometricBackground.beamCoefficients`, `OAI.BoltzmannNonuniqueness.JetComparisonCoefficient.coefficient`, `OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence`, `OAI.BoltzmannNonuniqueness.JetCopyDatum.ShrinkingCapFamily`, `OAI.BoltzmannNonuniqueness.WeakTime.Phase`, `OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotPairExtraction`, `OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.characteristicFrequency`, `OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction` and `OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.hotLimit` (definitions bundle `OAIQ080A000` of this split); `OAI.BoltzmannNonuniqueness.Published.DunfordPettis1940HotPairWindows`, `OAI.BoltzmannNonuniqueness.Published.GLPS1988Proposition3`, `OAI.BoltzmannNonuniqueness.Published.GPV2009CarlemanInput`, `OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalBeamKernel`, `OAI.BoltzmannNonuniqueness.WeakTime.phaseEndpointKernel` and `OAI.BoltzmannNonuniqueness.WeakTime.residenceKernel` (definitions bundle `OAIQ080A002` of this split); `OAI.BoltzmannNonuniqueness.Velocity` (the published bundle `Def_BoltzmannNonuniqueness`).
--
--   **Used by.** The proof of `OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotPairExtraction.entry_window_q80` of this split imports it.
-- source:
--   OpenAI, Nonuniqueness for the periodic hard-sphere Boltzmann equation (result family 363), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 363; paper: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/Nonuniqueness-for-the-periodic-hard-sphere-Boltzmann-equation-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/MathematicalPhysics/Boltzmann/Approximation/CapAnnularMassGrowth.lean (declaration OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotPairExtraction.positive_history_transfer)

import Mathlib
import Definitions.Def_BoltzmannNonuniqueness
import Definitions.Def_OAIQ080A002

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal ProbabilityTheory
open BoltzmannNonuniqueness.EuclideanFlight BoltzmannNonuniqueness.ReferenceGeometry
namespace BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence
variable {s₀ η K α γ d₀ q : ℝ} {F : ShrinkingCapFamily s₀ η K α γ d₀ q}
  {S : AttainedCapSequence F}

theorem HotPairExtraction.positive_history_transfer_q80
    (hDP : Published.DunfordPettis1940HotPairWindows)
    (hcarleman : Published.GPV2009CarlemanInput) (hGLPS : Published.GLPS1988Proposition3)
    (E : HotPairExtraction S)
    (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8) (hη : 0 < η) (hηmax : η ≤ Real.log 2)
    (hK : 0 ≤ K) (hα : 0 < α) (hαmax : α ≤ 1/4) (hγ : 0 < γ)
    (hd₀ : 0 < d₀) (hd₀max : d₀ ≤ 1)
    (hsmall : JetComparisonCoefficient.coefficient K*d₀*s₀^9 ≤ 1)
    (hq₁ : 1 < q) (hq₂ : q < 2)
    {a U V C r : ℝ} (ha : 0 < a) (haU : a < U) (hUV : U < V)
    (hV : ENNReal.ofReal V < E.horizon) (hC : 0 ≤ C) (hr : 0 < r)
    {β : WeakTime.Phase → ℝ} (hβ : ContDiff ℝ (⊤ : ℕ∞) β)
    (hβc : HasCompactSupport β) (hβn : ∀ p, 0 ≤ β p) (hβ₁ : ∀ p, β p ≤ 1)
    (hfrequency : ∀ u : CharacteristicPhase, u.1 ∈ Ioo a U → u.2 ∈ tsupport β →
      E.toHotLimitExtraction.characteristicFrequency u ≤ C)
    {Ω : Set CharacteristicPhase} (hΩ : MeasurableSet Ω) (hcore : ∀ z ∈ Ω, β z.2 = 1)
    (A B : ℝ → Set WeakTime.Phase) (hA : ∀ t, MeasurableSet (A t))
    (hB : ∀ s, MeasurableSet (B s))
    (hstart : ∀ s ∈ Ioo a U, ∀ p ∈ B s, β p = 1)
    (N : ℕ) (P : ℝ → ℝ → Prop)
    (horder : ∀ s ∈ Ioo a U, ∀ t ∈ Ioo a U, P s t → s ≤ t)
    (hpoint : ∀ s ∈ Ioo a U, ∀ t ∈ Ioo a U, P s t → ∀ p ∈ B s,
      0 < (WeakTime.phaseEndpointKernel C t ∘ₖ
        ((((localizedNormalBeamKernel
          (GeometricBackground.beamCoefficients (zero_lt_one.trans_le E.phase_mem.1)
            hα.le hγ.le η r) (K/(4*r)) C a η E.fraction hΩ).restrict
          (measurable_fst measurableSet_Ioc : MeasurableSet (Prod.fst ⁻¹' Ioc s t))) ∘ₖ
            WeakTime.residenceKernel C t)^N)) (s,p) (A t)) :
    ∀ᵐ s ∂volume, ∀ᵐ t ∂volume, s ∈ Ioo a U → t ∈ Ioo a U → P s t →
      0 < hotPhaseSlice E.hotLimit s (B s) → 0 < hotPhaseSlice E.hotLimit t (A t) := by
  sorry

end BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

end

end

end OAI
end
