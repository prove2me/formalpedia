-- Prove2me | Theorems.Thm_OAI_BoltzmannNonuniqueness_JetCopyDatum_selectedRemainder_gain_bound_q80
-- name    : OAI.BoltzmannNonuniqueness.JetCopyDatum.selectedRemainder_gain_bound_q80
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-31T19:27:47.807179+00:00
-- url     : https://prove2.me/theorems/354cb55f-e4ab-48f6-8773-6dd69b48a5a7
-- title:
--   OAI.BoltzmannNonuniqueness.JetCopyDatum.selectedRemainder_gain_bound_q80: intermediate lemma from OpenAI, Nonuniqueness for the periodic hard-sphere Boltzmann equation (result family 363)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.BoltzmannNonuniqueness.nonuniqueness`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Nonuniqueness for the periodic hard-sphere Boltzmann equation (result family 363)*, OpenAI Math Release, September 23, 2026, result family 363, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.BoltzmannNonuniqueness.JetCopyDatum.selectedRemainder_gain_bound` of [lean/OAI/MathematicalPhysics/Boltzmann/Compactness/SelectedNonaxialLimit.lean](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/MathematicalPhysics/Boltzmann/Compactness/SelectedNonaxialLimit.lean) at commit 1581d4c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.BoltzmannNonuniqueness.JetCopyDatum`, with `open MeasureTheory Set`, `open scoped ENNReal`, `open BoltzmannNonuniqueness.Published BoltzmannNonuniqueness.JetLattice`, `open BoltzmannNonuniqueness.VelocityWeight`):
--
--   ```lean
--   theorem selectedRemainder_gain_bound_q80 {r s₀ η K α γ d₀ q : ℝ} {N : ℕ}
--       (hr : 0 < r) (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8)
--       (hη : 0 < η) (hηmax : η ≤ Real.log 2) (hK : 0 ≤ K) (hα : 0 ≤ α)
--       (hd₀ : 0 < d₀) (hdmax : d₀ ≤ 1) (hq₁ : 1 < q) (hq₂ : q < 2)
--       (x : SpaceTime) (ht : 0 < x.1) {v : Velocity} (hv : transverse v ≠ 0) :
--       normalizedChartGain (volume.withDensity
--         (fun p => selectedRemainderDensity r s₀ η K α γ d₀ N (x,p))) q v ≤
--         ENNReal.ofReal r*(ENNReal.ofReal (JetRemainderSheet.uniformConstant K)*
--           SheetTotal.bound q (2*Real.exp (16*(1+α)^2)))
--   ```
--
--   **Definitions.** The statement is written with `OAI.BoltzmannNonuniqueness.JetCopyDatum.selectedRemainderDensity`, `OAI.BoltzmannNonuniqueness.JetRemainderSheet.uniformConstant`, `OAI.BoltzmannNonuniqueness.Published.SpaceTime`, `OAI.BoltzmannNonuniqueness.Published.Velocity`, `OAI.BoltzmannNonuniqueness.SheetTotal.bound`, `OAI.BoltzmannNonuniqueness.VelocityWeight.Transverse` and `OAI.BoltzmannNonuniqueness.VelocityWeight.transverse` (definitions bundle `OAIQ080A000` of this split); `OAI.BoltzmannNonuniqueness.normalizedChartGain` (definitions bundle `OAIQ080A002` of this split); `OAI.BoltzmannNonuniqueness.Velocity` (the published bundle `Def_BoltzmannNonuniqueness`).
--
--   **Used by.** The proof of `OAI.BoltzmannNonuniqueness.JetCopyDatum.CapApproximation.normalized_mixed_gain_le_positive_q80` of this split imports it.
-- source:
--   OpenAI, Nonuniqueness for the periodic hard-sphere Boltzmann equation (result family 363), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 363; paper: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/Nonuniqueness-for-the-periodic-hard-sphere-Boltzmann-equation-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/MathematicalPhysics/Boltzmann/Compactness/SelectedNonaxialLimit.lean (declaration OAI.BoltzmannNonuniqueness.JetCopyDatum.selectedRemainder_gain_bound)

import Mathlib
import Definitions.Def_BoltzmannNonuniqueness
import Definitions.Def_OAIQ080A002

section

attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.characteristicGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.retainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalWindowEvent_sFinite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section

open MeasureTheory Set
open scoped ENNReal
open BoltzmannNonuniqueness.Published BoltzmannNonuniqueness.JetLattice
open BoltzmannNonuniqueness.VelocityWeight

namespace BoltzmannNonuniqueness.JetCopyDatum

theorem selectedRemainder_gain_bound_q80 {r s₀ η K α γ d₀ q : ℝ} {N : ℕ}
    (hr : 0 < r) (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8)
    (hη : 0 < η) (hηmax : η ≤ Real.log 2) (hK : 0 ≤ K) (hα : 0 ≤ α)
    (hd₀ : 0 < d₀) (hdmax : d₀ ≤ 1) (hq₁ : 1 < q) (hq₂ : q < 2)
    (x : SpaceTime) (ht : 0 < x.1) {v : Velocity} (hv : transverse v ≠ 0) :
    normalizedChartGain (volume.withDensity
      (fun p => selectedRemainderDensity r s₀ η K α γ d₀ N (x,p))) q v ≤
      ENNReal.ofReal r*(ENNReal.ofReal (JetRemainderSheet.uniformConstant K)*
        SheetTotal.bound q (2*Real.exp (16*(1+α)^2))) := by
  sorry

end BoltzmannNonuniqueness.JetCopyDatum

end

end

end OAI
end
