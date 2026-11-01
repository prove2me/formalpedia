-- Prove2me | Theorems.Thm_OAI_BoltzmannNonuniqueness_JetCopyDatum_CapApproximation_rescaled_cold_measure_majorant_q80
-- name    : OAI.BoltzmannNonuniqueness.JetCopyDatum.CapApproximation.rescaled_cold_measure_majorant_q80
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-31T19:13:55.602609+00:00
-- url     : https://prove2.me/theorems/67fe230b-64f3-43c4-a8e5-80f8d7d149b3
-- title:
--   OAI.BoltzmannNonuniqueness.JetCopyDatum.CapApproximation.rescaled_cold_measure_majorant_q80 (OpenAI intermediate lemma)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.BoltzmannNonuniqueness.nonuniqueness`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Nonuniqueness for the periodic hard-sphere Boltzmann equation (result family 363)*, OpenAI Math Release, September 23, 2026, result family 363, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.BoltzmannNonuniqueness.JetCopyDatum.CapApproximation.rescaled_cold_measure_majorant` of [lean/OAI/MathematicalPhysics/Boltzmann/Compactness/SelectedRemainderMeasure.lean](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/MathematicalPhysics/Boltzmann/Compactness/SelectedRemainderMeasure.lean) at commit 1581d4c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.BoltzmannNonuniqueness.JetCopyDatum`, with `open MeasureTheory Set`, `open scoped ENNReal`, `open BoltzmannNonuniqueness.Published BoltzmannNonuniqueness.JetLattice`, `open BoltzmannNonuniqueness.VelocityWeight`):
--
--   ```lean
--   theorem CapApproximation.rescaled_cold_measure_majorant_q80 {s₀ η K α γ d₀ q T r : ℝ} {N : ℕ}
--       (F : CapApproximation s₀ η K α γ d₀ q T N)
--       (hr : 0 < r) (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8)
--       (hη : 0 < η) (hηmax : η ≤ Real.log 2)
--       (hK : 0 ≤ K) (hα : 0 ≤ α) (hγ : 0 ≤ γ) (hd₀ : 0 < d₀)
--       (hsmall : JetComparisonCoefficient.coefficient K*d₀*s₀^9 ≤ 1)
--       (hq : q < 2) (hT : 0 ≤ T) (hTmax : T ≤ 1/32)
--       (x : SpaceTime) (ht : r*x.1 ∈ Ioc 0 T) :
--       volume.withDensity (fun v => ENNReal.ofReal (r*(H q v*F.coldTotal
--         (r*x.1,(JetPeriodicDatum.spatialMap (r • x.2),v))))) ≤
--         selectedColdKernel r s₀ η K α γ d₀ N x+
--         volume.withDensity (fun v => selectedRemainderDensity r s₀ η K α γ d₀ N (x,v))+
--         volume.withDensity (fun v => ENNReal.ofReal
--           (r*(H q v*F.escapedTotal ((r*x.1,r • x.2),v))))
--   ```
--
--   **Definitions.** The statement is written with `OAI.BoltzmannNonuniqueness.JetComparisonCoefficient.coefficient`, `OAI.BoltzmannNonuniqueness.JetCopyDatum.CapApproximation`, `OAI.BoltzmannNonuniqueness.JetCopyDatum.selectedColdKernel`, `OAI.BoltzmannNonuniqueness.JetCopyDatum.selectedRemainderDensity`, `OAI.BoltzmannNonuniqueness.JetPeriodicDatum.spatialMap`, `OAI.BoltzmannNonuniqueness.JetPrototype.Phase`, `OAI.BoltzmannNonuniqueness.JetPrototype.Space`, `OAI.BoltzmannNonuniqueness.Published.SpaceTime`, `OAI.BoltzmannNonuniqueness.Published.Velocity`, `OAI.BoltzmannNonuniqueness.VelocityWeight.H`, `OAI.BoltzmannNonuniqueness.JetCopyDatum.CapApproximation.coldTotal` and `OAI.BoltzmannNonuniqueness.JetCopyDatum.CapApproximation.escapedTotal` (definitions bundle `OAIQ080A000` of this split); `OAI.BoltzmannNonuniqueness.Velocity` (the published bundle `Def_BoltzmannNonuniqueness`).
--
--   **Used by.** The proof of `OAI.BoltzmannNonuniqueness.JetCopyDatum.CapApproximation.normalized_mixed_gain_le_positive_q80` of this split imports it.
-- source:
--   OpenAI, Nonuniqueness for the periodic hard-sphere Boltzmann equation (result family 363), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 363; paper: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/Nonuniqueness-for-the-periodic-hard-sphere-Boltzmann-equation-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/MathematicalPhysics/Boltzmann/Compactness/SelectedRemainderMeasure.lean (declaration OAI.BoltzmannNonuniqueness.JetCopyDatum.CapApproximation.rescaled_cold_measure_majorant)

import Mathlib
import Definitions.Def_BoltzmannNonuniqueness
import Definitions.Def_OAIQ080A000

section

attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.characteristicGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.retainedKernel_sFinite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Set
open scoped ENNReal
open BoltzmannNonuniqueness.Published BoltzmannNonuniqueness.JetLattice
open BoltzmannNonuniqueness.VelocityWeight

namespace BoltzmannNonuniqueness.JetCopyDatum

theorem CapApproximation.rescaled_cold_measure_majorant_q80 {s₀ η K α γ d₀ q T r : ℝ} {N : ℕ}
    (F : CapApproximation s₀ η K α γ d₀ q T N)
    (hr : 0 < r) (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8)
    (hη : 0 < η) (hηmax : η ≤ Real.log 2)
    (hK : 0 ≤ K) (hα : 0 ≤ α) (hγ : 0 ≤ γ) (hd₀ : 0 < d₀)
    (hsmall : JetComparisonCoefficient.coefficient K*d₀*s₀^9 ≤ 1)
    (hq : q < 2) (hT : 0 ≤ T) (hTmax : T ≤ 1/32)
    (x : SpaceTime) (ht : r*x.1 ∈ Ioc 0 T) :
    volume.withDensity (fun v => ENNReal.ofReal (r*(H q v*F.coldTotal
      (r*x.1,(JetPeriodicDatum.spatialMap (r • x.2),v))))) ≤
      selectedColdKernel r s₀ η K α γ d₀ N x+
      volume.withDensity (fun v => selectedRemainderDensity r s₀ η K α γ d₀ N (x,v))+
      volume.withDensity (fun v => ENNReal.ofReal
        (r*(H q v*F.escapedTotal ((r*x.1,r • x.2),v)))) := by
  sorry

end BoltzmannNonuniqueness.JetCopyDatum

end

end OAI
end
