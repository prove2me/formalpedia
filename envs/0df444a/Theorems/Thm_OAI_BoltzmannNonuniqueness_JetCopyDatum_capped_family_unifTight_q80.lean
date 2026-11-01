-- Prove2me | Theorems.Thm_OAI_BoltzmannNonuniqueness_JetCopyDatum_capped_family_unifTight_q80
-- name    : OAI.BoltzmannNonuniqueness.JetCopyDatum.capped_family_unifTight_q80
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-31T19:13:45.9712+00:00
-- url     : https://prove2.me/theorems/4059f8cd-ba45-455b-a5bb-9b22b9421027
-- title:
--   OAI.BoltzmannNonuniqueness.JetCopyDatum.capped_family_unifTight_q80: intermediate lemma from OpenAI, Nonuniqueness for the periodic hard-sphere Boltzmann equation (result family 363)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.BoltzmannNonuniqueness.nonuniqueness`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Nonuniqueness for the periodic hard-sphere Boltzmann equation (result family 363)*, OpenAI Math Release, September 23, 2026, result family 363, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.BoltzmannNonuniqueness.JetCopyDatum.capped_family_unifTight` of [lean/OAI/MathematicalPhysics/Boltzmann/Approximation/CappedTightness.lean](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/MathematicalPhysics/Boltzmann/Approximation/CappedTightness.lean) at commit 1581d4c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.BoltzmannNonuniqueness.JetCopyDatum`, with `open MeasureTheory Set`, `open scoped ENNReal`, `open BoltzmannNonuniqueness.VelocityWeight BoltzmannNonuniqueness.WeightedLocalControl`):
--
--   ```lean
--   theorem capped_family_unifTight_q80 {s₀ η K α γ d₀ q T : ℝ}
--       (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8) (hη : 0 < η) (hηmax : η ≤ Real.log 2)
--       (hK : 0 ≤ K) (hα : 0 < α) (hαmax : α ≤ 1) (hγ : 0 < γ)
--       (hd₀ : 0 < d₀) (hd₀max : d₀ ≤ 1)
--       (hsmall : JetComparisonCoefficient.coefficient K*d₀*s₀^9 ≤ 1)
--       (hq : q < 2) (hT : 0 ≤ T) (hTmax : T ≤ 1/32)
--       (b L R δ : ℕ → ℝ) (h₀ : ℕ → JetPrototype.Phase → ℝ)
--       (hb : ∀ n, 0 ≤ b n) (hL : ∀ n, 0 ≤ L n) (hR : ∀ n, 0 ≤ R n)
--       (hδ : ∀ n, 0 < δ n) (hδmax : ∀ n, δ n ≤ 1)
--       (hloss : ∀ n, R n*CutoffLipschitz.frequencyConstant q (b n) ≤ L n)
--       (hh₀m : ∀ n, Measurable (h₀ n)) (hh₀ : ∀ n p, 0 ≤ h₀ n p)
--       (hF₀ : ∀ n p, initial s₀ η K α γ d₀ q n (h₀ n) p ≤ R n)
--       (F : ∀ n, PeriodicMildState q (b n) (L n) T (R n) (initial s₀ η K α γ d₀ q n (h₀ n)))
--       (hcap : ∀ n, (F n).hotPeak (δ n) (color s₀ η K α γ d₀ q n) ≤ 1) :
--       UnifTight (fun n => torusPhysical q (F n).value) 1
--         ((AnnularEnvelope.timePositionVolume T).prod (volume : Measure Velocity)) ∧
--       UnifTight (fun n => CollisionCompactness.pairDensity (torusPhysical q (F n).value)) 1
--         ((AnnularEnvelope.timePositionVolume T).prod (volume : Measure (Velocity × Velocity))) ∧
--       UnifTight (fun n => CollisionCompactness.gainDensity (torusPhysical q (F n).value)) 1
--         ((AnnularEnvelope.timePositionVolume T).prod (volume : Measure Velocity)) ∧
--       UnifTight (fun n => CollisionCompactness.lossDensity (torusPhysical q (F n).value)) 1
--         ((AnnularEnvelope.timePositionVolume T).prod (volume : Measure Velocity))
--   ```
--
--   **Definitions.** The statement is written with `OAI.UnifTight`, `OAI.BoltzmannNonuniqueness.AnnularEnvelope.timePositionVolume`, `OAI.BoltzmannNonuniqueness.CollisionCompactness.gainDensity`, `OAI.BoltzmannNonuniqueness.CollisionCompactness.lossDensity`, `OAI.BoltzmannNonuniqueness.CollisionCompactness.pairDensity`, `OAI.BoltzmannNonuniqueness.CutoffLipschitz.frequencyConstant`, `OAI.BoltzmannNonuniqueness.JetComparisonCoefficient.coefficient`, `OAI.BoltzmannNonuniqueness.JetCopyDatum.color`, `OAI.BoltzmannNonuniqueness.JetCopyDatum.initial`, `OAI.BoltzmannNonuniqueness.JetCopyDatum.instCountableLabel`, `OAI.BoltzmannNonuniqueness.JetCopyDatum.torusPhysical`, `OAI.BoltzmannNonuniqueness.JetLattice.Label`, `OAI.BoltzmannNonuniqueness.JetPrototype.Phase`, `OAI.BoltzmannNonuniqueness.JetPrototype.Space`, `OAI.BoltzmannNonuniqueness.VelocityWeight.Transverse`, `OAI.BoltzmannNonuniqueness.WeightedLocalControl.PeriodicMildState` and `OAI.BoltzmannNonuniqueness.WeightedLocalControl.PeriodicMildState.hotPeak` (definitions bundle `OAIQ080A000` of this split); `OAI.BoltzmannNonuniqueness.Position` and `OAI.BoltzmannNonuniqueness.Velocity` (the published bundle `Def_BoltzmannNonuniqueness`).
--
--   **Used by.** The proof of `OAI.BoltzmannNonuniqueness.JetCopyDatum.exists_tight_cap_family_at_q80` of this split imports it.
-- source:
--   OpenAI, Nonuniqueness for the periodic hard-sphere Boltzmann equation (result family 363), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 363; paper: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/Nonuniqueness-for-the-periodic-hard-sphere-Boltzmann-equation-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/MathematicalPhysics/Boltzmann/Approximation/CappedTightness.lean (declaration OAI.BoltzmannNonuniqueness.JetCopyDatum.capped_family_unifTight)

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

open MeasureTheory Set
open scoped ENNReal
open BoltzmannNonuniqueness.VelocityWeight BoltzmannNonuniqueness.WeightedLocalControl

namespace BoltzmannNonuniqueness.JetCopyDatum

theorem capped_family_unifTight_q80 {s₀ η K α γ d₀ q T : ℝ}
    (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8) (hη : 0 < η) (hηmax : η ≤ Real.log 2)
    (hK : 0 ≤ K) (hα : 0 < α) (hαmax : α ≤ 1) (hγ : 0 < γ)
    (hd₀ : 0 < d₀) (hd₀max : d₀ ≤ 1)
    (hsmall : JetComparisonCoefficient.coefficient K*d₀*s₀^9 ≤ 1)
    (hq : q < 2) (hT : 0 ≤ T) (hTmax : T ≤ 1/32)
    (b L R δ : ℕ → ℝ) (h₀ : ℕ → JetPrototype.Phase → ℝ)
    (hb : ∀ n, 0 ≤ b n) (hL : ∀ n, 0 ≤ L n) (hR : ∀ n, 0 ≤ R n)
    (hδ : ∀ n, 0 < δ n) (hδmax : ∀ n, δ n ≤ 1)
    (hloss : ∀ n, R n*CutoffLipschitz.frequencyConstant q (b n) ≤ L n)
    (hh₀m : ∀ n, Measurable (h₀ n)) (hh₀ : ∀ n p, 0 ≤ h₀ n p)
    (hF₀ : ∀ n p, initial s₀ η K α γ d₀ q n (h₀ n) p ≤ R n)
    (F : ∀ n, PeriodicMildState q (b n) (L n) T (R n) (initial s₀ η K α γ d₀ q n (h₀ n)))
    (hcap : ∀ n, (F n).hotPeak (δ n) (color s₀ η K α γ d₀ q n) ≤ 1) :
    UnifTight (fun n => torusPhysical q (F n).value) 1
      ((AnnularEnvelope.timePositionVolume T).prod (volume : Measure Velocity)) ∧
    UnifTight (fun n => CollisionCompactness.pairDensity (torusPhysical q (F n).value)) 1
      ((AnnularEnvelope.timePositionVolume T).prod (volume : Measure (Velocity × Velocity))) ∧
    UnifTight (fun n => CollisionCompactness.gainDensity (torusPhysical q (F n).value)) 1
      ((AnnularEnvelope.timePositionVolume T).prod (volume : Measure Velocity)) ∧
    UnifTight (fun n => CollisionCompactness.lossDensity (torusPhysical q (F n).value)) 1
      ((AnnularEnvelope.timePositionVolume T).prod (volume : Measure Velocity)) := by
  sorry

end BoltzmannNonuniqueness.JetCopyDatum

end

end

end OAI
end
